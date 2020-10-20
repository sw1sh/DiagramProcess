Package["DiagramProcess`"]

PackageExport["transposeProc"]
PackageExport["flattenProc"]
PackageExport["traceProc"]

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
    Proc[f, Map[reverseType, Reverse @ out], Map[reverseType, Reverse @ in],
        With[{label = getLabel[p]}, If[MatchQ[label, _Transpose], First @ label, Transpose[label]]],
        procTag[p]
    ]


flattenProc[p_Proc] := p //. Map[
    Function[head,
        q : Proc[Defer[head[left___, Proc[Defer[head[inside___]], __],right___]], __] :>
        MapAt[Defer[head[left, inside, right]] &, q, 1]
    ],
    {Composition, CircleTimes}
]


composeProcs[p : Proc[f_, fIn_, fOut_, ___], q : Proc[g_, gIn_, gOut_, ___]] :=
    Which[
     (*   fIn === {},
        Proc[Defer[p @* q], gIn, Join[fOut, gOut], getLabel[p] @* getLabel[q], Composition],

        gOut === {},
        Proc[Defer[p @* q], Join[fIn, gIn], fOut, getLabel[p] @* getLabel[q], Composition],
*)
        fIn === gOut,
        Proc[Defer[p @* q], gIn, fOut, getLabel[p] @* getLabel[q], Composition],

        True,
        Module[{
            in, out,
            F, G, perm
        },
        in = Join[ResourceFunction["MultisetComplement"][gOut, fIn], fIn];
        out = Join[gOut, ResourceFunction["MultisetComplement"][fIn, gOut]];
        F = CircleTimes @@ Append[identityProc /@ ResourceFunction["MultisetComplement"][in, fIn], p];
        G = CircleTimes @@ Prepend[identityProc /@ ResourceFunction["MultisetComplement"][out, gOut], q];
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
    q = If[in === out, identityProc[OverBar[in]], castProc[OverBar[in], OverBar[out]]];
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
