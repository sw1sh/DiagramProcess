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
PackageExport["doubleProc"]

PackageScope["compatibleProcsQ"]
PackageScope["composeProcs"]
PackageScope["procInArity"]
PackageScope["procOutArity"]
PackageScope["procArity"]
PackageScope["procArityWidth"]
PackageScope["procIn"]
PackageScope["procOut"]
PackageScope["procWidth"]
PackageScope["procHeight"]
PackageScope["unProc"]



transposeProc[Proc[Defer[Composition[ps__Proc]], ___]] := Composition @@ Reverse[transposeProc /@ {ps}]

transposeProc[Proc[Defer[CircleTimes[ps__Proc]], ___]] := CircleTimes @@ Reverse[transposeProc /@ {ps}]

transposeProc[p : Proc[f_, in_, out_, ___]] :=
    Proc[Labeled[procFunc[p], With[{label = procLabel[p]}, If[MatchQ[label, "Transpose"[_]], First @ label, "Transpose"[label]]]], Map[dualType, Reverse @ out], Map[dualType, Reverse @ in],
        procTag[p] /. {"cup" -> "cap", "cap" -> "cup"}
    ]


algebraicTransposeProc[Proc[Defer[Composition[ps__Proc]], ___]] := Composition @@ Reverse[algebraicTransposeProc /@ {ps}]

algebraicTransposeProc[Proc[Defer[CircleTimes[ps__Proc]], ___]] := CircleTimes @@ Reverse[algebraicTransposeProc /@ {ps}]

algebraicTransposeProc[p : Proc[f_, in_, out_, ___]] :=
    Proc[Labeled[procFunc[p], With[{label = procLabel[p]}, If[MatchQ[label, _Transpose], First @ label, Transpose[label]]]], Map[dualType, out], Map[dualType, in],
        procTag[p] /. {"cup" -> "cap", "cap" -> "cup"}
    ]


adjointProc[Proc[Defer[Composition[ps__Proc]], ___]] := Composition @@ Reverse[adjointProc /@ {ps}]

adjointProc[Proc[Defer[CircleTimes[ps__Proc]], ___]] := CircleTimes @@ Reverse[adjointProc /@ {ps}]

adjointProc[p : Proc[f_, in_, out_, ___]] :=
    Proc[Labeled[procFunc[p], With[{label = procLabel[p]}, If[MatchQ[label, _SuperDagger], First @ label, SuperDagger[label]]]], Map[dualType, out], Map[dualType, in],
        procTag[p] /. {"cup" -> "cap", "cap" -> "cup"}
    ]


conjugateProc[p_Proc] := transposeProc[adjointProc[p]] /. "Transpose"[SuperDagger[l_]] :> OverBar[l]


compositeProc[p_Proc] := Proc[Labeled[procFunc[p], "Composite"[procLabel[p]]], procInput[p], procOutput[p], procTag[p]]


doubleProc[p_Proc] := With[{q = CircleTimes[conjugateProc[p], p]}, compositeProc[curryProc[procOutput[q]] @* q @* uncurryProc[procInput[q]]]]


stripProcSupers[expr_] := expr //. "Transpose"[l_] | Transpose[l_] | SuperDagger[l_] | OverBar[l_] :> l


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
        Proc[Defer[p @* q], gIn, fOut, Composition],

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


unProc[p_Proc] := unLabel[p //. Proc[op_, __] :> op /. Defer -> Identity]


procInArity[Proc[_, in_, ___]] := Length[in]

procOutArity[Proc[_, _, out_, ___]] := Length[out]

procArity[Proc[_, in_, out_, ___]] := Max[Length[in], Length[out]]

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
