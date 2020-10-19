Package["DiagramProcess`"]

PackageExport["transposeProc"]

PackageScope["flattenProc"]
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
        fIn === {},
        Proc[Defer[p \[CircleTimes] q], gIn, Join[fOut, gOut], getLabel[p] \[CircleTimes] getLabel[q], CircleTimes],

        gOut === {},
        Proc[Defer[p \[CircleTimes] q], Join[fIn, gIn], fOut, getLabel[p] \[CircleTimes] getLabel[q], CircleTimes],

        fIn === gOut,
        Proc[Defer[p @* q], gIn, fOut, getLabel[p] @* getLabel[q], Composition],
        True,
        Module[{
            alignment,
            aligned,
            outEnds, inEnds,
            outIds, inIds,
            F, G
        },
        alignment = SequenceAlignment[gOut, fIn];
        aligned = Catenate @ Cases[alignment, {Except[_List] ..}, 1];
        outEnds = Catenate @ Cases[alignment, {x_List, {}} :> x, 1];
        inEnds = Catenate @ Cases[alignment, {{}, y_List} :> y, 1];
        outIds = Join[Catenate @ Cases[alignment, {x_List, Except[{}]} :> x, 1], Complement[outEnds, inEnds]];
        inIds = Join[Catenate@Cases[alignment, {Except[{}], y_List} :> y, 1], Complement[inEnds, outEnds]];
        F = CircleTimes @@ Append[Map[identityProc, outIds], p];
        G = CircleTimes @@ Prepend[Map[identityProc, inIds], q];
        With[{perm = FindPermutation[Join[outIds, fIn], Join[gOut, inIds]]},
            If[OrderedQ @ PermutationList[perm],
                F @* G,
                F @* permutationProc[perm, Join[gOut, inIds]] @* G
            ]
        ]
   ]
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
