Package["DiagramProcess`"]

PackageExport["ProcTensor"]



ProcTensor[p_Proc] /; procTagQ[p, "double"] := ProcTensor[unDoubleProc[p]]


ProcTensor[p_Proc] /; procTagQ[p, "composite"] := ProcTensor[stripComposites[p]]


ProcTensor[p : Proc[Except[_Defer], in_, out_, ___]] := Module[{
    interpretation = procInterpretation[p],
    label = procLabel[p],
    inDimensions, outDimensions, dimensions,
    tensor
},
    inDimensions = procInputDimensions[p];
    outDimensions = procOutputDimensions[p];
    dimensions = procDimensions[p];
    tensor = Which[
        procTagQ[p, "id" | "curry"],
        IdentityMatrix[Times @@ inDimensions],

        procTagQ[p, "permutation"],
        TensorTranspose[ArrayReshape[IdentityMatrix[Times @@ inDimensions], dimensions], procData[p][[2]]],

(*        procTagQ[p, "cup"] && procRotatedQ[p] && Length[in] == 2,
        With[{basis = typeBasis /@ in}, Sum[KroneckerProduct[basis[[1, i]], basis[[2, i]]], {i, Length[basis[[1]]]}]],

        procTagQ[p, "cup"] && Length[out] == 2,
        With[{basis = typeBasis /@ out}, Sum[KroneckerProduct[basis[[1, i]], basis[[2, i]]], {i, Length[basis[[1]]]}]],
*)

        (* double/quantum spider *)
        procTagQ[p, "spider" | "cup"] && SameQ @@ typeDimensions /@ Join[out, in] && AllTrue[typeDimensions /@ Join[out, in], Length[#] == 2 &],
        With[{basis = typeBasis @ First @ Join[out, in], arity = procArity[p]},
            Total[KroneckerProduct @@ Table[#, arity] & /@ basis]
        ],

        (* classical and bastard spider *)
        procTagQ[p, "spider" | "cup"] && SameQ @@ typeDimensions /@ Flatten @ Join[typeList /@ out, typeList /@ in],
        With[{basis = typeBasis[#, False] & /@ Join[out, in], dim = First @ typeDimensions @ First @ Join[out, in]},
            Sum[KroneckerProduct @@ (#[[Sequence @@ Table[i, TensorRank[#] / 2]]] & /@ basis), {i, dim}]
        ],

        ArrayQ[interpretation] && Times @@ Dimensions[interpretation] == Times @@ dimensions,
        interpretation,

        Times @@ dimensions == 1,
        interpretation,

        True,
        Array[label, dimensions]
    ];
    If[ ArrayQ[tensor],
        tensor = ArrayReshape[tensor, dimensions]
    ];
    If[ ArrayQ[tensor] && procTagQ[p, "transpose"],
        With[{n = Length[outDimensions], m = Length[inDimensions]},
            tensor = TensorTranspose[tensor, Join[Range[m] + n, Range[n]]]
        ]
    ];
    If[ procTagQ[p, "adjoint"],
        tensor = Conjugate[tensor]
    ];
    tensor
]

ProcTensor[p : Proc[Defer[CircleTimes[ps__Proc]], in_, out_, ___]] :=
    ArrayReshape[KroneckerProduct @@ wrap @* ProcTensor /@ {ps}, Catenate[typeDimensions /@ Join[out, in]]]


ProcTensor[p : Proc[Defer[Composition[ps__Proc]], ___]] := Fold[
    With[{n = Length @ Catenate[typeDimensions /@ procOutput[#2]], m = TensorRank[#1]},
        TensorContract[TensorProduct[#1, ProcTensor[#2]], {m - n, m} + # & /@ Range[n]]
    ] &,
    ProcTensor[First @ {ps}],
    Rest @ {ps}
]


ProcTensor[Proc[Defer[Plus[ps__Proc]], ___]] := Total[ProcTensor /@ {ps}]
