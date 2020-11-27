Package["DiagramProcess`"]

PackageExport["ProcTensor"]
PackageExport["ProcMatrix"]


ProcTensor[p_Proc] /; procTagQ[p, "double"] := ProcTensor[unDoubleProc[p]]


ProcTensor[p_Proc] /; procTagQ[p, "composite"] := ProcTensor[unCompositeProc[p]]


ProcTensor[p : Proc[_Labeled, ___]] := ProcTensor[MapAt[unLabel, p, {1}]]


ProcTensor[p : Proc[Except[_Defer], ___]] := Module[{
    in = procInput[p], out = procOutput[p],
    interpretation = procInterpretation[p],
    inDimensions, pInDimensions, outDimensions, dimensions,
    tensor
},
    inDimensions = procInputDimensions[p, True];
    pInDimensions = typeDimension /@ procInput[p, True];
    outDimensions = procOutputDimensions[p, True];
    dimensions = procDimensions[p, True];
    tensor = Which[
        procTagQ[p, "id" | "curry"],
        IdentityMatrix[Times @@ inDimensions],

        procTagQ[p, "permutation"],
        With[{id = ArrayReshape[KroneckerProduct @@ IdentityMatrix /@ pInDimensions, Join[pInDimensions, pInDimensions]]},
            TensorTranspose[id, procData[p]["Permutation"]]
        ],

        procTagQ[p, "cup"],
        With[{basis = typeBasis[First @ Join[out, in], True, True]},
            Total[kroneckerProduct[#, #] & /@ basis]
        ],

        procTagQ[p, "spider"  | "discard"] && SameQ @@ typeDimensions /@ Flatten @ Join[typeList /@ out, typeList /@ in] && Length[dimensions] > 0,
        With[{dim = First @ typeDimensions @ First @ Join[out, in]},
        With[{phase = If[MissingQ[procData[p]["Phase"]], Table[1, dim],
            If[ ListQ[procData[p]["Phase"]],
                Prepend[Exp[I wrap[procData[p]["Phase"]]], 1],
                Prepend[Table[Exp[I procData[p]["Phase"]], dim - 1], 1]
            ]]},
            If[ MissingQ[procData[p]["Basis"]],
                With[{basis = typeBasis[#, True, False] & /@ Join[out, in]},
                    Sum[phase[[i]] kroneckerProduct @@ (#[[Sequence @@ Table[i, TensorRank[#] - 2]]] & /@ basis), {i, dim}]
                ],
                With[{basis = First @ procData[p]["Basis"]},
                    Sum[phase[[i]] kroneckerProduct @@ Table[basis[[i]], Length[dimensions]], {i, dim}]
                ]
            ]
        ]],

        procTagQ[p, "empty"],
        1,

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
    If[ ArrayQ[tensor] && procTagQ[p, "algebraic transpose"],
        With[{n = Length[outDimensions], m = Length[inDimensions]},
            tensor = TensorTranspose[tensor, Join[Range[m] + n, Range[n]]]
        ]
    ];
    If[ procTagQ[p, "dual"],
        tensor = Conjugate[tensor]
    ];
    (*Echo[{p, dimensions, If[ ArrayQ[tensor], ArrayReshape[tensor, {Times @@ outDimensions, Times @@ inDimensions}] //MatrixForm, tensor]}];*)
    tensor
]

ProcTensor[p : Proc[Defer[CircleTimes[ps__]], ___]] :=
    ArrayReshape[KroneckerProduct @@ ProcMatrix /@ {ps}, procDimensions[p, True]]


ProcTensor[p : Proc[Defer[Composition[ps__]], ___]] :=
    ArrayReshape[Dot @@ ProcMatrix /@ {ps}, procDimensions[p, True]]


ProcTensor[Proc[Defer[Plus[ps__]], ___]] := Total[ProcTensor /@ {ps}]


ProcMatrix[p_Proc] := Module[{tensor = ProcTensor[p], matrix},
    matrix = If[ ArrayQ[tensor],
        (* Normal due to some weird bug in 12.1 *)
        ArrayReshape[Normal @ tensor, {Times @@ procOutputDimensions[p], Times @@ procInputDimensions[p]}],
        {{tensor}}
    ];
    matrix
]


kroneckerProduct[ts___] := Fold[If[ArrayQ[#1] && ArrayQ[#2], KroneckerProduct[##], Times[##]] &, {ts}]
