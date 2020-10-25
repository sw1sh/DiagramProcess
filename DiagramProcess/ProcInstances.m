Package["DiagramProcess`"]

PackageScope["topologicalProcQ"]
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
PackageScope["withTerminals"]



topologicalProcQ[p_Proc] := MatchQ[procTag[p], "empty" | "id" | "cast" | "permutation" | "cup" | "cap" | "copy" | "initial" | "terminal"]


emptyProc[] := Proc[Labeled[{} &, "\[EmptySet]"], {}, {}, "empty"]


zeroProc[] := Proc[Labeled[0 &, "0"], {}, {}, "zero"]


identityProc[in_] := Proc[Labeled[Identity, Labeled[Unique["id"], "1"]], {SystemType @ in}, {SystemType @ in}, "id"]


castProc[in_, out_] := Proc[Labeled["Cast", Labeled[Unique["cast"], "1"]], {SystemType @ in}, {SystemType @ out}, "cast"]


permutationProc[perm_Cycles, in_List] := With[{
    ps = PermutationList[perm, Length[in]],
    invPerm = InversePermutation @ perm,
    inTypes = SystemType /@ in
},
    Proc[Labeled[Permute[{##}, invPerm] &, Labeled[Unique["pi"], Subscript["\[Pi]", Row @ ps]]], inTypes, Permute[inTypes, invPerm], "permutation"]
]


swapProc[A_, B_] := permutationProc[Cycles[{{1, 2}}], {A, B}]


cupProc[out_] := Proc[Labeled["Cup", Labeled[Unique["cup"], "\[Union]"]], {}, {dualType @ SystemType[out], SystemType[out]}, "cup"]


capProc[in_] := ReplacePart[transposeProc @ cupProc[in], {1 -> Labeled["Cap", Labeled[Unique["cap"], "\[Intersection]"]], -1 -> "cap"}]


copyProc[in_, n_ : 2] := Proc[Labeled[{#, #} &, Labeled[Unique["copy"], "\[Gamma]"]], {SystemType[in]}, Table[SystemType[in], n], "copy"]


sumProc[i_] := Proc[Labeled["Sum", Labeled[Unique["sum"], Subscript["\[CapitalSigma]", i]]], {}, {}, "sum"]


withTerminals[p : Proc[f_, in_, out_, ___]] := Module[{
   q,
   initial = Proc[Labeled[unWrap[{##}] &, Labeled[Unique["initial"], "\[ScriptCapitalI]"]], in, in, "initial"],
   terminal = Proc[Labeled[unWrap[{##}] &, Labeled[Unique["terminal"], "\[ScriptCapitalT]"]], out, out, "terminal"]
},
    q = If[Length @ out > 0, terminal @* p, p];
    flattenProc @ If[Length[in] > 0, q @* initial, q]
]
