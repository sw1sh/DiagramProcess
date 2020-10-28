Package["DiagramProcess`"]

PackageExport["topologicalProcQ"]
PackageExport["unlabeledProcQ"]
PackageExport["zeroProc"]
PackageExport["emptyProc"]
PackageExport["identityProc"]
PackageExport["castProc"]
PackageExport["permutationProc"]
PackageExport["swapProc"]
PackageExport["cupProc"]
PackageExport["capProc"]
PackageExport["copyProc"]
PackageExport["sumProc"]
PackageExport["uncurryProc"]
PackageExport["curryProc"]
PackageExport["discardProc"]

PackageExport["withTerminals"]



topologicalProcQ[p_Proc] := procTagQ[p, "empty" | "id" | "cast" | "permutation" | "cup" | "cap" | "copy" | "initial" | "terminal"]


unlabeledProcQ[p_Proc] := procTagQ[p, "empty" | "id" | "cast" | "permutation" | "cup" | "cap" |
    "copy" | "initial" | "terminal" | "curry" | "uncurry" | "discard"]


emptyProc[] := Proc[Labeled[{} &, "\[EmptySet]"], {}, {}, {"empty"}]


zeroProc[] := Proc[Labeled[0 &, "0"], {}, {}, {"zero"}]


identityProc[in_] := Proc[Labeled[Identity, "1"], {SystemType @ in}, {SystemType @ in}, {"id"}, Unique["id"]]


castProc[in_, out_] := Proc[Labeled["Cast", "1"], {SystemType @ in}, {SystemType @ out}, {"cast"}, Unique["cast"]]


permutationProc[perm_Cycles, in_List] := With[{
    ps = PermutationList[perm, Length[in]],
    invPerm = InversePermutation @ perm,
    inTypes = SystemType /@ in
},
    Proc[Labeled[Permute[{##}, invPerm] &, Subscript["\[Pi]", Row @ ps]], inTypes, Permute[inTypes, invPerm], {"permutation"}, Unique["pi"]]
]


swapProc[A_, B_] := permutationProc[Cycles[{{1, 2}}], {A, B}]


cupProc[out_] := Proc[Labeled["Cup", "\[Union]"], {}, {dualType @ SystemType[out], SystemType[out]}, {"cup"}, Unique["cup"]]


capProc[in_] := mapProcLabel["\[Intersection]" &, transposeProc @ cupProc[in]]


copyProc[in_, n_ : 2] := Proc[Labeled[{#, #} &, "\[Gamma]"], {SystemType[in]}, Table[SystemType[in], n], {"copy"}, Unique["copy"]]


sumProc[i_] := Proc[Labeled["Sum", Subscript["\[CapitalSigma]", i]], {}, {}, {"sum"}, Unique["sum"]]


uncurryProc[ts_List] := Proc[Labeled[Replace[#, CircleTimes -> List, Heads -> True] &, "uncurry"], {Apply[CircleTimes, SystemType /@ ts]}, SystemType /@ ts, {"uncurry"}, Unique["uncurry"]]


curryProc[ts_List] := Proc[Labeled[Apply[CircleTimes], "curry"], SystemType /@ ts, {Apply[CircleTimes, SystemType /@ ts]}, {"curry"}, Unique["curry"]]


discardProc[t_] := Proc[Labeled[{} &, "discard"], {CircleTimes[SystemType[t], SystemType[t]]}, {}, {"discard"}, Unique["discard"]]


withTerminals[p : Proc[f_, in_, out_, ___]] := Module[{
   q,
   initial = Proc[Labeled[unWrap[{##}] &, "\[ScriptCapitalI]"], in, in, {"initial"}, Unique["initial"]],
   terminal = Proc[Labeled[unWrap[{##}] &, "\[ScriptCapitalT]"], out, out, {"terminal"}, Unique["terminal"]]
},
    q = If[Length @ out > 0, terminal @* p, p];
    flattenProc @ If[Length[in] > 0, q @* initial, q]
]
