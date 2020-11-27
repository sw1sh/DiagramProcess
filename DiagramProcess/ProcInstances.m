Package["DiagramProcess`"]

PackageScope["withTerminals"]
PackageScope["topologicalProcQ"]
PackageScope["unlabeledProcQ"]
PackageScope["zeroProc"]
PackageScope["emptyProc"]
PackageScope["identityProc"]
PackageScope["castProc"]
PackageScope["permutationProc"]
PackageScope["swapProc"]
PackageScope["cupProc"]
PackageScope["capProc"]
PackageScope["copyProc"]
PackageScope["sumProc"]
PackageScope["uncurryProc"]
PackageScope["curryProc"]
PackageScope["discardProc"]
PackageScope["maximallyMixedProc"]
PackageScope["procBasis"]
PackageScope["spiderProc"]
PackageScope["dimensionProc"]
PackageScope["xSpiderProc"]
PackageScope["zSpiderProc"]
PackageScope["hadamardProc"]
PackageScope["measureProc"]
PackageScope["encodeProc"]


withTerminals[p_Proc] := Module[{
    in = procInput[p, True],
    out = procOutput[p, True],
    q,
    initial, terminal
},
    initial = Proc[Labeled[unWrap[{##}] &, "\[ScriptCapitalI]"], in, in, <|"Tags" -> {"terminal", "topological"}, "Id" -> Unique["initial"]|>];
    terminal = Proc[Labeled[unWrap[{##}] &, "\[ScriptCapitalT]"], out, out, <|"Tags" -> {"terminal", "topological"}, "Id" -> Unique["terminal"]|>];
    q = If[Length @ out > 0, terminal @* p, p];
    flattenProc @ If[Length[in] > 0, q @* initial, q]
]


topologicalProcQ[p_Proc] := procTagQ[p, "topological"]


unlabeledProcQ[p_Proc] := procTagQ[p, "empty" | "id" | "cast" | "permutation" | "cup" |
    "copy" | "terminal" | "curry" | "discard"] || procTagQ[p, {"spider", "topological"}]


emptyProc[] := Proc[Labeled[{} &, "\[EmptySet]"], {}, {}, <|"Tags" -> {"empty"}, "Id" -> Unique["empty"]|>]


zeroProc[] := Proc[Labeled[0 &, "0"], {}, {}, <|"Tags" -> {"zero"}, "Id" -> Unique["zero"]|>]


identityProc[in_] := Proc[Labeled[Identity, "1"], {SystemType @ in}, {SystemType @ in}, <|"Tags" -> {"id", "topological"}, "Id" -> Unique["id"]|>]


castProc[in_, out_] := Proc[Labeled["Cast", "1"], {SystemType @ in}, {SystemType @ out}, <|"Tags" -> {"cast"}, "Id" -> Unique["cast"]|>]


permutationProc[perm_Cycles, in_List] := With[{
    ps = PermutationList[InversePermutation @ perm, Length[in]],
    inTypes = SystemType /@ in
},
    Proc[Labeled[Permute[{##}, perm] &, Subscript["\[Pi]", Row @ ps]], inTypes, Permute[inTypes, perm],
         <|"Tags" -> {"permutation", "topological"}, "Id" -> Unique["pi"], "Permutation" -> perm|>]
]


swapProc[A_, B_] := permutationProc[Cycles[{{1, 2}}], {A, B}]


cupProc[out__] := Proc[Labeled["Cup", "\[Union]"], {}, {Sequence @@ dualType @* SystemType /@ Reverse[{out}], Sequence @@ SystemType /@ {out}}, <|"Tags" -> {"cup", "topological"}, "Id" -> Unique["cup"]|>]


capProc[in__] := mapProcLabel["\[Intersection]" &, adjointProc[dualProc @ cupProc[in]]]


copyProc[in_, n_ : 2] := Proc[Labeled[Table[#, n] &, "copy"], {SystemType[in]}, Table[SystemType[in], n], <|"Tags" -> {"spider", "topological"}, "Id" -> Unique["copy"]|>]


matchProc[ts__] := mapProcLabel["match" &, adjointProc[dualProc @ copyProc[ts]]]


sumProc[i_] := Proc[Labeled["Sum", Subscript["\[CapitalSigma]", i]], {}, {}, <|"Tags" -> {"sum"}, "Id" -> Unique["sum"]|>]


uncurryProc[ts__] := mapProcLabel["uncurry" &, adjointProc[dualProc @ curryProc[ts]]]


curryProc[ts__] := Proc[Labeled[List, "curry"], SystemType /@ {ts}, {Apply[CircleTimes, SystemType /@ {ts}]}, <|"Tags" -> {"curry", "topological"}, "Id" -> Unique["curry"]|>]


discardProc[t_] := Proc[Labeled[{} &, "discard"], {CircleTimes[dualType @ SystemType[t], SystemType[t]]}, {}, <|"Tags" -> {"discard"}, "Id" -> Unique["discard"]|>]


maximallyMixedProc[t_] := mapProcLabel["mix" &, adjointProc @ dualProc @ discardProc[t]]


procBasis[t_, n_Integer] := Table[Proc[Superscript[i, t]], {i, n}]


spiderProc[phase_, in_List, out_List] := Proc[Labeled[phase, If[phase =!= 0, phase, "\[EmptyCircle]"]],
    SystemType /@ in, SystemType /@ out, <|"Tags" -> {"spider", If[phase === 0, "topological", Nothing]}, "Id" -> Unique["spider"], "Phase" -> phase|>]

spiderProc[in_List, out_List] := spiderProc[0, in, out]

spiderProc[phase_, n_, m_, t_] := spiderProc[phase, Table[t, n], Table[t, m]]

spiderProc[n_, m_, t_] := spiderProc[0, n, m, t]


zSpiderProc[args__] := With[{p = spiderProc[args]}, If[procData[p]["Phase"] === 0, p, unsetProcTag[p, "topological"]]]

xSpiderProc[args__] := Module[{
    p = mapProcLabel[If[# === "\[EmptyCircle]", Style["\[FilledCircle]", Gray], #] & , zSpiderProc[args]],
    t,
    dim
},
    t = First @ typeList @ First @ procTypes[p];
    dim = Times @@ typeDimensions[p];
    setProcData[p, "Basis" -> xBasis[{t}]]
]

xBasis[ts_List] := Map[
    With[{dim = Times @@ typeDimensions[#1]},
        Table[ProcMatrix[zSpiderProc[j Subdivide[2 Pi, dim][[2 ;; -2]], 0, 1, #]] / Sqrt[dim], {j, dim, 1, -1}]
    ] &,
    SystemType /@ ts
]

hadamardProc[t_] := Proc[Labeled[HadamardMatrix[Times @@ typeDimensions[SystemType[t]]], "H"],
    {SystemType[t]}, {SystemType[t]}, <|"Tags" -> {}, "Id" -> Unique["hadamard"]|>]


measureProc[t_] := Proc["Measure", {CircleTimes[dualType @ SystemType[t], SystemType[t]]}, {SystemType[t]}, <|"Tags" -> {"spider", "topological"}, "Id" -> Unique["measure"]|>]

encodeProc[t_] := mapProcLabel["Encode" &, adjointProc[measureProc[dualType @ SystemType @ t]]]

deleteProc[t_] := Proc[Labeled[{} &, "Delete"], {SystemType[t]}, {}, <|"Tags" -> {"spider", "topological"}, "Id" -> Unique["delete"]|>]

createProc[t_] := mapProcLabel["Create" &, adjointProc[deleteProc[dualType @ SystemType @ t]]]

dimensionProc[t_] := Proc[Times @@ typeDimensions[SystemType[t]], {}, {}, <|"Tags" -> {"spider", "topological"}, "Id" -> Unique["dimension"]|>]


Proc["Composite"[p_, args___]] := compositeProc[Proc[p], args]

Proc["Circuit"[p_]] := replaceUnderHold[Proc[p], q_Proc :> setProcTag[q, "circuit"]]

Proc["Double"[p_]] := doubleProc[Proc[p]]

Proc["Dual"[p_]] := dualProc[Proc[p]]

Proc["Transpose"[f_]] := algebraicTransposeProc @ Proc[f]

Proc["Tr"[p_, args___]] := traceProc[Proc[p], args]


Proc["Zero"] := zeroProc[]

Proc["Empty"] := emptyProc[]

Proc[("Identity" | "Id" | "\[Delta]")[a_]] := identityProc[a]

Proc[("Cap" | "\[Intersection]" | "\[Cap]")[a__]] := capProc[a]

Proc[("Cup" | "\[Union]" | "\[Cup]")[a__]] := cupProc[a]

Proc["Permutation"[perm_Cycles, in_List]] := permutationProc[perm, in]

Proc["Swap"[a_, b_]] := swapProc[a, b]

Proc["Copy"[a_]] := copyProc[a]

Proc["Match"[a_]] := matchProc[a]

Proc["Uncurry"[as__]] := uncurryProc[as]

Proc["Curry"[as__]] := curryProc[as]

Proc["Discard"[a_]] := discardProc[a]

Proc["MaximallyMixed"[a_]] := maximallyMixedProc[a]

Proc["Spider"[args : Repeated[_, {3, 4}]]] := spiderProc[args]

Proc["Spider"[in_List, out_List]] := setProcData[setProcTag[Proc[Subsuperscript["\[EmptyCircle]", in, out]], {"spider", "topological"}], "Id" -> Unique["spider"]]

Proc["Spider"[p_]] := setProcTag[Proc[p], {"spider"}]

Proc["CircuitId"[t_]] := setProcTag[spiderProc[{1, t}, {t, 1}], {"id", "circuit"}]

Proc["Dimension"[t_]] := dimensionProc[t]

Proc["XSpider"[args___]] := xSpiderProc[args]

Proc["ZSpider"[args___]] := zSpiderProc[args]

Proc["XBasis"[args___]] := With[{p = Proc[args]},
    replaceUnderHold[p, q_Proc /; procTagQ[q, "spider"] :> setProcData[q, "Basis" -> xBasis[{First @ typeList @ First @ procTypes[q]}]]]
]

Proc["Hadamard"[args___]] := hadamardProc[args]

Proc["Measure"[a_]] := measureProc[a]

Proc["Encode"[a_]] := encodeProc[a]

Proc["Delete"[a_]] := deleteProc[a]

Proc["Decoherence"[a_]] := encodeProc[a] @* measureProc[a]

Proc["LeviCevita"[n_Integer, t_]] := Proc[Labeled[LeviCivitaTensor[n], "\[CurlyEpsilon]"], Table[SystemType[t, "Dimensions" -> {n}], n], {}, <|"Id" -> Unique["levicevita"], "Tags" -> {}|>]

Proc["CNOT"[a_]] := With[{t = SystemType[a]},
    mapProcLabel["CNOT" &,
        Proc[Labeled[Sqrt[typeDimension[t]], Sqrt[typeDimension[t]]] \[CircleTimes] "Circuit"[("Spider"[{1, t}, {t, t}] \[CircleTimes] "CircuitId"[t]) /* ("CircuitId"[t] \[CircleTimes] "XSpider"[{t, t}, {t, 1}])]]
    ]
]

Proc["QCNOT"[a_]] := With[{t = SystemType[a]},
    mapProcLabel["CNOT" &,
        Proc[typeDimension[t] \[CircleTimes] "Circuit"[("Double"["Spider"[{1, t}, {t, t}]] \[CircleTimes] "Double"["CircuitId"[t]]) /*
            ("Double"["CircuitId"[t]] \[CircleTimes] "Double"["XSpider"[{t, t}, {t, 1}]])]
        ]
    ]
]
