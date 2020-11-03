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
PackageScope["xSpiderProc"]
PackageScope["zSpiderProc"]
PackageScope["measureProc"]
PackageScope["encodeProc"]


withTerminals[p : Proc[f_, in_, out_, ___]] := Module[{
   q,
   initial = Proc[Labeled[unWrap[{##}] &, "\[ScriptCapitalI]"], in, in, {"initial", "topological"}, Unique["initial"]],
   terminal = Proc[Labeled[unWrap[{##}] &, "\[ScriptCapitalT]"], out, out, {"terminal", "topological"}, Unique["terminal"]]
},
    q = If[Length @ out > 0, terminal @* p, p];
    flattenProc @ If[Length[in] > 0, q @* initial, q]
]


topologicalProcQ[p_Proc] := procTagQ[p, "topological"]


unlabeledProcQ[p_Proc] := procTagQ[p, "empty" | "id" | "cast" | "permutation" | "cup" | "cap" |
    "copy" | "initial" | "terminal" | "curry" | "uncurry" | "discard"] || procTagQ[p, {"spider", "topological"}]


emptyProc[] := Proc[Labeled[{} &, "\[EmptySet]"], {}, {}, {"empty"}]


zeroProc[] := Proc[Labeled[0 &, "0"], {}, {}, {"zero"}]


identityProc[in_] := Proc[Labeled[Identity, "1"], {SystemType @ in}, {SystemType @ in}, {"id", "topological"}, Unique["id"]]


castProc[in_, out_] := Proc[Labeled["Cast", "1"], {SystemType @ in}, {SystemType @ out}, {"cast"}, Unique["cast"]]


permutationProc[perm_Cycles, in_List] := With[{
    ps = PermutationList[perm, Length[in]],
    invPerm = InversePermutation @ perm,
    inTypes = SystemType /@ in
},
    Proc[Labeled[Permute[{##}, invPerm] &, Subscript["\[Pi]", Row @ ps]], inTypes, Permute[inTypes, invPerm], {"permutation", "topological"}, Unique["pi"] -> invPerm]
]


swapProc[A_, B_] := permutationProc[Cycles[{{1, 2}}], {A, B}]


cupProc[out_] := Proc[Labeled["Cup", "\[Union]"], {}, {dualType @ SystemType[out], SystemType[out]}, {"cup", "topological"}, Unique["cup"]]


capProc[in_] := mapProcLabel["\[Intersection]" &, transposeProc @ cupProc[in]]


copyProc[in_, n_ : 2] := Proc[Labeled[Table[#, n] &, "\[Gamma]"], {SystemType[in]}, Table[SystemType[in], n], {"spider", "topological"}, Unique["copy"]]


matchProc[args__] := adjointProc[copyProc[args]]


sumProc[i_] := Proc[Labeled["Sum", Subscript["\[CapitalSigma]", i]], {}, {}, {"sum"}, Unique["sum"]]


uncurryProc[ts_List] := Proc[Labeled[Replace[#, CircleTimes -> List, {1}, Heads -> True] &, "uncurry"], {Apply[CircleTimes, SystemType /@ ts]}, SystemType /@ ts,
    {"curry", "adjoint"}, Unique["uncurry"]]


curryProc[ts_List] := Proc[Labeled[CircleTimes, "curry"], SystemType /@ ts, {Apply[CircleTimes, SystemType /@ ts]}, {"curry"}, Unique["curry"]]


discardProc[t_] := Proc[Labeled[{} &, "discard"], {CircleTimes[SystemType[t], SystemType[t]]}, {}, {"discard"}, Unique["discard"]]


maximallyMixedProc[t_] := mapProcLabel["mix" &, transposeProc @ discardProc[t]]


procBasis[t_, n_Integer] := Table[Proc[Superscript[i, t]], {i, n}]


spiderProc[x_, t_, n_Integer, m_Integer] := Proc[Labeled["Spider", x], Table[SystemType[t], n], Table[SystemType[t], m], {"spider"}, Unique["spider"]]


xSpiderProc[args__] := setProcTag[spiderProc[args], "shaded"]

zSpiderProc[args__] := spiderProc[args]


measureProc[t_] := Proc["Measure", {CircleTimes[SystemType[t], SystemType[t]]}, {SystemType[t]}, {"spider", "topological"}, Unique["measure"]]

encodeProc[t_] := mapProcLabel["Encode" &, adjointProc[measureProc[t]]]

deleteProc[t_] := Proc[Labeled[{} &, "delete"], {SystemType[t]}, {}, {"spider", "topological"}, Unique["delete"]]


Proc["Composite"[p_, args___]] := compositeProc[Proc[p], args]

Proc["Double"[p_]] := doubleProc[Proc[p]]


Proc["Zero"] := zeroProc[]

Proc["Empty"] := emptyProc[]

Proc[("Identity" | "Id" | "\[Delta]")[a_]] := identityProc[a]

Proc[("Cap" | "\[Intersection]" | "\[Cap]")[a_]] := capProc[a]

Proc[("Cup" | "\[Union]" | "\[Cup]")[a_]] := cupProc[a]

Proc["Permutation"[perm_Cycles, in_List]] := permutationProc[perm, in]

Proc["Swap"[a_, b_]] := swapProc[a, b]

Proc["Copy"[a_]] := copyProc[a]

Proc["Match"[a_]] := matchProc[a]

Proc["Uncurry"[as_List]] := uncurryProc[as]

Proc["Curry"[as_List]] := curryProc[as]

Proc["Discard"[a_]] := discardProc[a]

Proc["XSpider"[phase_, n_, m_, t_]] := xSpiderProc[Style[phase, Bold], t, n, m]

Proc["ZSpider"[phase_, n_, m_, t_]] := zSpiderProc[phase, t, n, m]

Proc["Measure"[a_]] := measureProc[a]

Proc["Encode"[a_]] := encodeProc[a]

Proc["Delete"[a_]] := deleteProc[a]
