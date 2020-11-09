Package["DiagramProcess`"]

PackageExport["ProcTensor"]
PackageExport["ProcMatrix"]


ProcTensor[p_Proc] /; procTagQ[p, "double"] := ProcTensor[unDoubleProc[p]]


ProcTensor[p_Proc] /; procTagQ[p, "composite"] := ProcTensor[unCompositeProc[p]]


ProcTensor[p_Proc] /; procTagQ[p, "dual"] := Conjugate @ ProcTensor[unsetProcTag[p, "dual"]]


ProcTensor[p : Proc[_Labeled, ___]] := ProcTensor[MapAt[unLabel, p, {1}]]


ProcTensor[p : Proc[Except[_Defer], in_, out_, ___]] := Module[{
    interpretation = procInterpretation[p],
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

        (* classical and bastard spider *)
        procTagQ[p, "spider" | "cup" | "discard"] && SameQ @@ typeDimensions /@ Flatten @ Join[typeList /@ out, typeList /@ in] && Length[dimensions] > 0,
        With[{basis = typeBasis[#, True, False] & /@ Join[out, in], dim = First @ typeDimensions @ First @ Join[out, in]},
            Sum[kroneckerProduct @@ (#[[Sequence @@ Table[i, TensorRank[#] / 2]]] & /@ basis), {i, dim}]
        ],

        ArrayQ[interpretation] && Times @@ Dimensions[interpretation] == Times @@ dimensions,
        interpretation,

        Times @@ dimensions == 1,
        interpretation,

        True,
        Array[interpretation, dimensions]
    ];
    If[ ArrayQ[tensor],
        tensor = ArrayReshape[tensor, dimensions]
    ];
    If[ ArrayQ[tensor] && procTagQ[p, "transpose" | "algebraic transpose"],
        With[{n = Length[outDimensions], m = Length[inDimensions]},
            tensor = TensorTranspose[tensor, Join[Range[m] + n, Range[n]]]
        ]
    ];
    If[ procTagQ[p, "adjoint"],
        tensor = Conjugate[tensor]
    ];
    tensor
]

ProcTensor[p : Proc[Defer[CircleTimes[ps__]], in_, out_, ___]] :=
    ArrayReshape[KroneckerProduct @@ ProcMatrix /@ {ps}, procDimensions[p]]


ProcTensor[p : Proc[Defer[Composition[ps__]], ___]] :=
    ArrayReshape[Dot @@ ProcMatrix /@ {ps}, procDimensions[p]]


ProcTensor[Proc[Defer[Plus[ps__]], ___]] := Total[ProcTensor /@ {ps}]


ProcMatrix[p_Proc] := Module[{tensor = ProcTensor[p], matrix},
    matrix = If[ ArrayQ[tensor],
        ArrayReshape[tensor, {Times @@ procOutputDimensions[p], Times @@ procInputDimensions[p]}],
        {{tensor}}
    ];
    matrix
]


kroneckerProduct[ts___] := Fold[If[ArrayQ[#1] && ArrayQ[#2], KroneckerProduct[##], Times[##]] &, {ts}]
