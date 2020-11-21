Package["DiagramProcess`"]

PackageExport["transposeProc"]
PackageExport["algebraicTransposeProc"]
PackageExport["adjointProc"]
PackageExport["conjugateProc"]
PackageExport["algebraicConjugateProc"]
PackageExport["dualProc"]
PackageExport["stripProcLabel"]
PackageExport["flattenProc"]
PackageExport["traceProc"]
PackageExport["procToState"]
PackageExport["procToEffect"]
PackageExport["compositeProc"]
PackageExport["unCompositeProc"]
PackageExport["doubleProc"]
PackageExport["unDoubleProc"]

PackageExport["mapProcLabel"]
PackageExport["setProcTag"]
PackageExport["unsetProcTag"]

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


unsetProcTag[p_Proc, tag_] := MapAt[DeleteCases[tag], p, {-1, Key["Tags"]}]


setProcTag[p_Proc, tag : "transpose" | "algebraic transpose" | "adjoint" | "algebraic adjoint" | "dual"] /; procTagQ[p, tag] := unsetProcTag[p, tag]

setProcTag[p_Proc, tag : "composition" | "parallel composition" | "plus" | "sum"] /; procTagQ[p, "composition" | "parallel composition" | "plus" | "sum"] :=
    setProcTag[unsetProcTag[p, "composition" | "parallel composition" | "plus" | "sum"], tag]

setProcTag[p_Proc, tag_] := If[procTagQ[p, tag], p, MapAt[Append[tag], p, {-1, Key["Tags"]}]]

setProcTag[p_Proc, tags_List] := Fold[setProcTag, p, tags]


procRotatedQ[p_Proc] := Apply[Xor, procTagQ[p, #] & /@ {"transpose", "algebraic transpose", "adjoint", "algebraic adjoint"}]


transposeProc[p : Proc[_, in_, out_, ___]] := With[{f = Replace[procInterpretation[p], {
    Defer[Composition[ps__Proc]] :> procInterpretation[Composition @@ Reverse[transposeProc /@ {ps}]],
    Defer[CircleTimes[ps__Proc]] :> procInterpretation[CircleTimes @@ Reverse[transposeProc /@ {ps}]],
    Defer[Plus[ps__Proc]] :> procInterpretation[Plus @@ Reverse[transposeProc /@ {ps}]]
}]},
    setProcTag[Proc[Labeled[f, Transpose[procLabel[p]]],
        Map[dualType @* reverseType, Reverse @ out], Map[dualType @* reverseType, Reverse @ in],
        procTags[p], procData[p]], "transpose"]
]


algebraicTransposeProc[p : Proc[_, in_, out_, ___]] := With[{f = Replace[procInterpretation[p], {
    Defer[Composition[ps__Proc]] :> procInterpretation[Composition @@ Reverse[algebraicTransposeProc /@ {ps}]],
    Defer[CircleTimes[ps__Proc]] :> procInterpretation[CircleTimes @@ Reverse[algebraicTransposeProc /@ {ps}]],
    Defer[Plus[ps__Proc]] :> procInterpretation[Plus @@ Reverse[algebraicTransposeProc /@ {ps}]]
}]},
    setProcTag[Proc[Labeled[f, Transpose[procLabel[p]]],
        out, in,
        procTags[p], procData[p]], "algebraic transpose"]
]


adjointProc[p : Proc[_, in_, out_, ___]] := With[{f = Replace[procInterpretation[p], {
    Defer[Composition[ps__Proc]] :> procInterpretation[Composition @@ Reverse[adjointProc /@ {ps}]],
    Defer[CircleTimes[ps__Proc]] :> procInterpretation[CircleTimes @@ adjointProc /@ {ps}],
    Defer[Plus[ps__Proc]] :> procInterpretation[Plus @@ adjointProc /@ {ps}]
}]},
    setProcTag[Proc[Labeled[f, SuperDagger[procLabel[p]]], Map[dualType, out], Map[dualType, in], procTags[p], procData[p]], "adjoint"]
]


conjugateProc[p_Proc] := mapProcLabel[Replace[SuperDagger[Transpose[l_]] :> OverBar[l]], adjointProc[transposeProc[p]]]


algebraicConjugateProc[p_Proc] := mapProcLabel[Replace[SuperDagger[Transpose[l_]] :> OverBar[l]], adjointProc[algebraicTransposeProc[p]]]


dualProc[p : Proc[_, in_, out_, ___]] := With[{f = Replace[procInterpretation[p], {
    Defer[Composition[ps__Proc]] :> procInterpretation[Composition @@ dualProc /@ {ps}],
    Defer[CircleTimes[ps__Proc]] :> procInterpretation[CircleTimes @@ dualProc /@ {ps}],
    Defer[Plus[ps__Proc]] :> procInterpretation[Plus @@ dualProc /@ {ps}]
}]},
    setProcTag[Proc[Labeled[f, procLabel[p]], Map[dualType, in], Map[dualType, out], procTags[p], procData[p]], "dual"]
]


compositeProc[p_Proc, label_] := setProcTag[mapProcLabel[Framed[Interpretation[label, #]] &, p], "composite"]

compositeProc[p_Proc] := compositeProc[p, procLabel[p]]


unCompositeProc[p_Proc] /; procTagQ[p, "composite"] := mapProcLabel[ReplaceAll[Framed[Interpretation[_, l_]] :> l], unsetProcTag[p, "composite"]]

unCompositeProc[p_Proc] := p


doublePermutation[n_Integer] := FindPermutation[Catenate @ Thread[{Reverse[Range[n]], Range[n + 1, 2 n]}]]

doubleProc[p_Proc] := Module[{
    label = procLabel[p],
    q,
    cp
},
    If[procTagQ[p, "double"], Return[p]];
    cp = dualProc @ conjugateProc[p];
    q = CircleTimes[cp, mapProcLabel["Doubled", p]];
    If[ Length[procOutput[q, True]] > 0,
        Module[{perm = InversePermutation @ doublePermutation[Length[procOutput[p, True]]], pi},
            pi = permutationProc[perm, Join[procOutput[cp, True], procOutput[p, True]]];
            If[! OrderedQ[PermutationList[perm]],
                q = pi @* q;
            ];
            q = Apply[CircleTimes, Apply[curryProc] /@ Partition[procOutput[pi, True], 2]] @* q
        ]
    ];
    If[ Length[procInput[q, True]] > 0,
        Module[{perm = doublePermutation[Length[procInput[p, True]]], pi},
            pi = permutationProc[perm, Permute[Join[procInput[cp, True], procInput[p, True]], perm]];
            If[! OrderedQ[PermutationList[perm]],
                q = q @* pi
            ];
            q = q @* Apply[CircleTimes, Apply[uncurryProc] /@ Partition[procInput[pi, True], 2]]
        ];

    ];
    unsetProcTag[setProcTag[setProcData[mapProcLabel[Style[OverHat[label], Bold] &, q], Append[procData[p], "Double" -> p]], "double"], "circuit"]
]


unDoubleProc[p_Proc] /; procTagQ[p, "double"] := mapProcLabel[ReplaceAll[Style[OverHat[l_], Bold] :> l], unsetProcTag[p, "double"]]

unDoubleProc[p_Proc] := p


stripProcLabel[expr_] := expr //. Transpose[l_] | SuperDagger[l_] | OverBar[l_] | Framed[l_] :> l


flattenProc[p_Proc] := p //. Map[
    Function[head,
        q : Proc[Defer[head[left___, Proc[Defer[head[inside___]], __],right___]], __] :>
        MapAt[Defer[head[left, inside, right]] &, q, 1]
    ],
    {Composition, CircleTimes, Plus}
]


composeProcs[p_Proc, q_Proc] := Module[{
    pIn = procInput[p],
    pOut = procOutput[p, True],
    qIn = procInput[q, True],
    qOut = procOutput[q]
},
    Which[
        pIn === qOut,
        Proc[Defer[p @* q], qIn, pOut, <|"Tags" -> {"composition"}|>],

        True,
        Module[{
            in, out,
            P, Q, perm
        },
        in = With[{l = ResourceFunction["MultisetComplement"][qOut, pIn]}, Insert[l, Splice[pIn], FirstPosition[l, First[pIn, None]] /. _Missing -> -1]];
        out = With[{l = ResourceFunction["MultisetComplement"][pIn, qOut]}, Insert[l, Splice[qOut], FirstPosition[l, First[qOut, None]] /. _Missing -> 1]];
        P = CircleTimes @@ Insert[identityProc /@ ResourceFunction["MultisetComplement"][in, pIn], p, FirstPosition[in, First[pIn, None]] /. _Missing -> -1];
        Q = CircleTimes @@ Insert[identityProc /@ ResourceFunction["MultisetComplement"][out, qOut], q, FirstPosition[out, First[qOut, None]] /. _Missing -> 1];
        perm = FindPermutation[procInput[P], procOutput[Q]];
        If[OrderedQ @ PermutationList[perm],
            P @* Q,
            P @* permutationProc[perm, procOutput[Q]] @* Q
        ]
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


procInArity[Proc[_, in_, ___], includeEmpty_ : False] := If[includeEmpty, Length[in], Count[in, t_ /; typeArity[t] > 0]]

procOutArity[Proc[_, _, out_, ___], includeEmpty_ : False] := If[includeEmpty, Length[out], Count[out, t_ /; typeArity[t] > 0]]

procArity[p_Proc, includeEmpty_ : False] := Max[procInArity[p, includeEmpty], procOutArity[p, includeEmpty]]


procInTypeArity[Proc[_, in_, ___]] := Total[typeArity /@ in]

procOutTypeArity[Proc[_, _, out_, ___]] := Total[typeArity /@ out]

procTypeArity[p_Proc] := procInTypeArity[p] + procOutTypeArity[p]


procArityWidth[p_Proc] := procArity[p]
procArityWidth[Proc[Labeled[Defer[CircleTimes[ps__]], _] | Defer[CircleTimes[ps__]], __]] := Total[procArityWidth /@ {ps}]
procArityWidth[Proc[Labeled[Defer[Composition[ps__]], _] | Defer[Composition[ps__]], __]] := Max[procArityWidth /@ {ps}]


procWidth[_Proc] := 1
procWidth[Proc[Labeled[Defer[CircleTimes[ps__]], _] | Defer[CircleTimes[ps__]], __]] := Total @ Map[procWidth, {ps}]
procWidth[Proc[Labeled[Defer[Composition[ps__]], _] | Defer[Composition[ps__]], __]] := Max @ Map[procWidth, {ps}]


procWidths[_Proc] := {1}
procWidths[Proc[Labeled[Defer[CircleTimes[ps__]], _] | Defer[CircleTimes[ps__]], __]] := {Map[procWidth, {ps}]}
procWidths[Proc[Labeled[Defer[Composition[ps__]], _] | Defer[Composition[ps__]], __]] := Catenate @ Map[procWidths, {ps}]


procHeight[_Proc] := 1
procHeight[Proc[Labeled[Defer[CircleTimes[ps__]], _] | Defer[CircleTimes[ps__]], __]] := Max @ Map[procHeight, {ps}]
procHeight[Proc[Labeled[Defer[Composition[ps__]], _] | Defer[Composition[ps__]], __]] := Total @ Map[procHeight, {ps}]


procHeights[_Proc] := {1}
procHeights[Proc[Labeled[Defer[CircleTimes[ps__]], _] | Defer[CircleTimes[ps__]], __]] := Catenate @ Map[procHeights, {ps}]
procHeights[Proc[Labeled[Defer[Composition[ps__]], _] | Defer[Composition[ps__]], __]] := {Map[procHeight, {ps}]}


procIn[p_Proc ? (procTagQ["double" | "composite"]), includeEmpty_ : False] := {p -> procInput[p, includeEmpty]}
procIn[Proc[Labeled[Defer[CircleTimes[ps__Proc]], _] | Defer[CircleTimes[ps__Proc]], ___], includeEmpty_ : False] := Catenate[procIn[#, includeEmpty] & /@ {ps}]
procIn[Proc[Labeled[Defer[Composition[ps__Proc]], _] | Defer[Composition[ps__Proc]], ___], includeEmpty_ : False] := procIn[Last @ {ps}, includeEmpty]
procIn[Proc[Labeled[Defer[Plus[ps__Proc]], _] | Defer[Plus[ps__Proc]], ___], includeEmpty_ : False] := procIn[First @ {ps}, includeEmpty]
procIn[p_Proc, includeEmpty_ : False] := {p -> procInput[p, includeEmpty]}


procOut[p_Proc ? (procTagQ["double" | "composite"]), includeEmpty_ : False] := {p -> procOutput[p, includeEmpty]}
procOut[Proc[Labeled[Defer[CircleTimes[ps__Proc]], _] | Defer[CircleTimes[ps__Proc]], ___], includeEmpty_ : False] := Catenate[procOut[#, includeEmpty] & /@ {ps}]
procOut[Proc[Labeled[Defer[Composition[ps__Proc]], _] | Defer[Composition[ps__Proc]], ___], includeEmpty_ : False] := procOut[First @ {ps}, includeEmpty]
procOut[Proc[Labeled[Defer[Plus[ps__Proc]], _] | Defer[Plus[ps__Proc]], ___], includeEmpty_ : False] := procOut[First @ {ps}. includeEmpty]
procOut[p_, includeEmpty_ : False] := {p -> procOutput[p, includeEmpty]}


procInputDimensions[p_Proc] := Catenate[typeDimensions /@ procInput[p]]

procOutputDimensions[p_Proc] := Catenate[typeDimensions /@ procOutput[p]]

procDimensions[p_Proc] := Join[procOutputDimensions[p], procInputDimensions[p]];
