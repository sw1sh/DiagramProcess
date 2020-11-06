Package["DiagramProcess`"]

PackageExport["transposeProc"]
PackageExport["algebraicTransposeProc"]
PackageExport["adjointProc"]
PackageExport["conjugateProc"]
PackageExport["stripProcSupers"]
PackageExport["flattenProc"]
PackageExport["traceProc"]
PackageExport["procToState"]
PackageExport["procToEffect"]
PackageExport["compositeProc"]
PackageExport["stripComposites"]
PackageExport["doubleProc"]
PackageExport["unDoubleProc"]

PackageScope["mapProcLabel"]
PackageScope["setProcTag"]
PackageScope["unsetProcTag"]

PackageScope["procRotatedQ"]
PackageScope["compatibleProcsQ"]
PackageScope["composeProcs"]
PackageScope["procInArity"]
PackageScope["procOutArity"]
PackageScope["procArity"]
PackageScope["procInTypeArity"]
PackageScope["procOutTypeArity"]
PackageScope["procTypeArity"]
PackageScope["procArityWidth"]
PackageScope["procIn"]
PackageScope["procOut"]
PackageScope["procWidth"]
PackageScope["procHeight"]
PackageScope["procInputDimensions"]
PackageScope["procOutputDimensions"]
PackageScope["procDimensions"]

PackageScope["unProc"]



mapProcLabel[f_, p_Proc] := ReplacePart[p, 1 -> Labeled[procInterpretation[p], f[procLabel[p]]]]


unsetProcTag[p_Proc, tag_] := MapAt[DeleteCases[tag], p, {4}]


setProcTag[p_Proc, tag : "transpose" | "algebraic transpose" | "adjoint"] /; procTagQ[p, tag] := unsetProcTag[p, tag]

setProcTag[p_Proc, tag : "composition" | "parallel composition" | "plus" | "sum"] /; procTagQ[p, "composition" | "parallel composition" | "plus" | "sum"] :=
    setProcTag[unsetProcTag[p, "composition" | "parallel composition" | "plus" | "sum"], tag]

setProcTag[p_Proc, tag_] := If[procTagQ[p, tag], p, MapAt[Append[tag], p, {4}]]

setProcTag[p_Proc, tags_List] := Fold[setProcTag, p, tags]


procRotatedQ[p_Proc] := Apply[Xor, procTagQ[p, #] & /@ {"transpose", "algebraic transpose", "adjoint"}]


transposeProc[Proc[Defer[Composition[ps__Proc]], ___]] := Composition @@ Reverse[transposeProc /@ {ps}]

transposeProc[Proc[Defer[CircleTimes[ps__Proc]], ___]] := CircleTimes @@ Reverse[transposeProc /@ {ps}]

transposeProc[p : Proc[_, in_, out_, ___]] :=
    setProcTag[ReplacePart[mapProcLabel[Transpose, p], {2 -> Map[dualType, Reverse @ out], 3 -> Map[dualType, Reverse @ in]}], "transpose"]


algebraicTransposeProc[Proc[Defer[Composition[ps__Proc]], ___]] := Composition @@ Reverse[algebraicTransposeProc /@ {ps}]

algebraicTransposeProc[Proc[Defer[CircleTimes[ps__Proc]], ___]] := CircleTimes @@ Reverse[algebraicTransposeProc /@ {ps}]

algebraicTransposeProc[p : Proc[_, in_, out_, ___]] :=
    setProcTag[ReplacePart[mapProcLabel[Transpose, p], {2 -> out, 3 -> in}], "algebraic transpose"]


adjointProc[Proc[Defer[Composition[ps__Proc]], ___]] := Composition @@ Reverse[adjointProc /@ {ps}]

adjointProc[Proc[Defer[CircleTimes[ps__Proc]], ___]] := CircleTimes @@ adjointProc /@ {ps}

adjointProc[p : Proc[_, in_, out_, ___]] :=
    setProcTag[ReplacePart[mapProcLabel[SuperDagger, p], {2 -> Map[dualType, out], 3 -> Map[dualType, in]}], "adjoint"]


conjugateProc[p_Proc] := replaceUnderHold[transposeProc[adjointProc[p]], Transpose[SuperDagger[l_]] :> OverBar[l]]


compositeProc[p_Proc, label_] := mapProcLabel[label &, setProcTag[p, "composite"]]

compositeProc[p_Proc] := compositeProc[p, procLabel[p]]

compositeProc[p_Proc, label_, data_] := setProcData[compositeProc[p, label], data]


stripComposites[p_Proc] := replaceUnderHold[p, q_Proc /; procTagQ[q, "composite"] :> MapAt[First, unsetProcTag[q, "composite"], {1}]]


doublePermutation[n_Integer] := FindPermutation[Catenate @ Thread[{Reverse[Range[n]], Range[n + 1, 2 n]}]]

doubleProc[p_Proc] := Module[{
    label = procLabel[p],
    q,
    cp = conjugateProc[p]
},
    q = CircleTimes[cp, p];
    If[ Length[procOutput[q]] > 0,
        Module[{perm = InversePermutation @ doublePermutation[Length[procOutput[p]]], pi},
            pi = permutationProc[perm, Join[procOutput[cp], procOutput[p]]];
            If[! OrderedQ[PermutationList[perm]],
                q = pi @* q;
            ];
            q = Apply[CircleTimes, Apply[curryProc] /@ Partition[procOutput[pi], 2]] @* q
        ]
    ];
    If[ Length[procInput[q]] > 0,
        Module[{perm = doublePermutation[Length[procInput[p]]], pi},
            pi = permutationProc[perm, Permute[Join[procInput[cp], procInput[p]], perm]];
            If[! OrderedQ[PermutationList[perm]],
                q = q @* pi
            ];
            q = q @* Apply[CircleTimes, Apply[uncurryProc] /@ Partition[procInput[pi], 2]]
        ];

    ];
    setProcData[setProcTag[mapProcLabel[Style[OverHat[label], Bold] &, q], Append[procTags[p], "double"]], p]
]


unDoubleProc[p_Proc] /; procTagQ[p, "double"] := MapAt[unLabel, unsetProcTag[p, "double"], {1}](*replaceUnderHold[p, q_Proc /; procTagQ[q, "double"] :> MapAt[unLabel, unsetProcTag[q, "double"], {1}]]*)

unDoubleProc[p_Proc] := p


stripProcSupers[expr_] := expr //. Transpose[l_] | SuperDagger[l_] | OverBar[l_] :> l


flattenProc[p_Proc] := p //. Map[
    Function[head,
        q : Proc[Defer[head[left___, Proc[Defer[head[inside___]], __],right___]], __] :>
        MapAt[Defer[head[left, inside, right]] &, q, 1]
    ],
    {Composition, CircleTimes, Plus}
]


composeProcs[p : Proc[f_, fIn_, fOut_, ___], q : Proc[g_, gIn_, gOut_, ___]] :=
    Which[
        fIn === gOut,
        Proc[Defer[p @* q], gIn, fOut, {"composition"}],

        True,
        Module[{
            in, out,
            F, G, perm
        },
        in = With[{l = ResourceFunction["MultisetComplement"][gOut, fIn]}, Insert[l, Splice[fIn], FirstPosition[l, First[fIn, None]] /. _Missing -> -1]];
        out = With[{l = ResourceFunction["MultisetComplement"][fIn, gOut]}, Insert[l, Splice[gOut], FirstPosition[l, First[gOut, None]] /. _Missing -> 1]];
        F = CircleTimes @@ Insert[identityProc /@ ResourceFunction["MultisetComplement"][in, fIn], p, FirstPosition[in, First[fIn, None]] /. _Missing -> -1];
        G = CircleTimes @@ Insert[identityProc /@ ResourceFunction["MultisetComplement"][out, gOut], q, FirstPosition[out, First[gOut, None]] /. _Missing -> 1];
        perm = FindPermutation[F[[2]], G[[3]]];
        If[OrderedQ @ PermutationList[perm],
            F @* G,
            F @* permutationProc[perm, G[[3]]] @* G
        ]
        ]
   ]


traceProc[p_Proc, ii_Integer : 1, jj_Integer : 1] := Module[{
    i = Max[Min[ii, Length[p[[2]]]], 1],
    j = Max[Min[jj, Length[p[[3]]]], 1],
    in, out, q
},
    in = p[[2, i]];
    out = p[[3, j]];
    q = If[in === out, identityProc[dualType[in]], castProc[dualType[in], dualType[out]]];
    Composition @@ {
        CircleTimes @@ Prepend[identityProc /@ Drop[p[[3]], {j}], capProc[out]],
        CircleTimes[q, Composition @@ {
            If[j > 1,
                permutationProc[Cycles[{{1, j}}], p[[3]]],
                Nothing
            ],
            p,
            If[i > 1,
                permutationProc[Cycles[{{1, i}}], Permute[p[[2]], Cycles[{{1, i}}]]],
                Nothing
            ]
       }],
        CircleTimes @@ Prepend[identityProc /@ Drop[p[[2]], {i}], cupProc[in]]
    }
]


procToState[p_Proc] := With[{cups = cupProc /@ p[[2]]}, Fold[
    CircleTimes[identityProc[dualType[#1[[2, 1]]]], #1] @* CircleTimes[#2, Sequence @@ Map[identityProc, #1[[2, 2 ;;]]]] &, p, cups]]


procToEffect[p_Proc] := With[{caps = capProc /@ p[[3]]}, Fold[
    CircleTimes[#2, Sequence @@ Map[identityProc, #1[[3, 2 ;;]]]] @* CircleTimes[identityProc[dualType[#1[[3, 1]]]], #1] &, p, caps]]


compatibleProcsQ[ps__Proc] := Equal @@ Map[#[[2]] &, {ps}] && Equal @@ Map[#[[3]] &, {ps}]


unProc[p_Proc] := unLabelAll[p //. Proc[op_, __] :> op /. Defer[x_] :> x]


procInArity[Proc[_, in_, ___]] := Length[in]

procOutArity[Proc[_, _, out_, ___]] := Length[out]

procArity[Proc[_, in_, out_, ___]] := Max[Length[in], Length[out]]


procInTypeArity[Proc[_, in_, ___]] := Total[typeArity /@ in]

procOutTypeArity[Proc[_, _, out_, ___]] := Total[typeArity /@ out]

procTypeArity[p_Proc] := procInTypeArity[p] + procOutTypeArity[p]


procArityWidth[p_Proc] := procArity[p]
procArityWidth[Proc[Defer[Composition[ps__]], __]] := Max[procArityWidth /@ {ps}]
procArityWidth[Proc[Defer[CircleTimes[ps__]], __]] := Total[procArityWidth /@ {ps}]


procWidth[_Proc] := 1
procWidth[Proc[Defer[Composition[ps__]], __]] := Max @ Map[procWidth, {ps}]
procWidth[Proc[Defer[CircleTimes[ps__]], __]] := Total @ Map[procWidth, {ps}]


procWidths[_Proc] := {1}
procWidths[Proc[Defer[Composition[ps__]], __]] := Catenate @ Map[procWidths, {ps}]
procWidths[Proc[Defer[CircleTimes[ps__]], __]] := {Map[procWidth, {ps}]}


procHeight[_Proc] := 1
procHeight[Proc[Defer[CircleTimes[ps__]], __]] := Max @ Map[procHeight, {ps}]
procHeight[Proc[Defer[Composition[ps__]], __]] := Total @ Map[procHeight, {ps}]


procHeights[_Proc] := {1}
procHeights[Proc[Defer[CircleTimes[ps__]], __]] := Catenate @ Map[procHeights, {ps}]
procHeights[Proc[Defer[Composition[ps__]], __]] := {Map[procHeight, {ps}]}


procIn[Proc[Defer[CircleTimes[ps__Proc]], ___]] := Catenate[procIn /@ {ps}]
procIn[Proc[Defer[Composition[ps__Proc]], ___]] := procIn @ Last @ {ps}
procIn[p : Proc[_, in_, ___]] := {p -> in}


procOut[Proc[Defer[CircleTimes[ps__Proc]], ___]] := Catenate[procOut /@ {ps}]
procOut[Proc[Defer[Composition[ps__Proc]], ___]] := procOut @ First@{ps}
procOut[p : Proc[_, _, out_, ___]] := {p -> out}


procInputDimensions[p_Proc] := Catenate[typeDimensions /@ procInput[p]]

procOutputDimensions[p_Proc] := Catenate[typeDimensions /@ procOutput[p]]

procDimensions[p_Proc] := Join[procOutputDimensions[p], procInputDimensions[p]];
