Package["DiagramProcess`"]

PackageExport["emptyProc"]
PackageExport["identityProc"]
PackageExport["castProc"]
PackageExport["permutationProc"]
PackageExport["swapProc"]
PackageExport["cupProc"]
PackageExport["capProc"]
PackageExport["copyProc"]
PackageExport["withTerminals"]



emptyProc[] := Proc[Labeled[{} &, Labeled[Unique["empty"], "\[EmptySet]"]], {}, {}, "empty"]


identityProc[in_] := Proc[Labeled[Identity, Labeled[Unique["\[Delta]"], "1"]], {SystemType @ in}, {SystemType @ in}, "id"]


castProc[in_, out_] := Proc[Labeled["Cast", Labeled[Unique["cast"], "1"]], {SystemType @ in}, {SystemType @ out}, "cast"]


permutationProc[perm_Cycles, in_List] := With[{
    ps = PermutationList[perm, Length[in]],
    invPerm = InversePermutation @ perm,
    inTypes = SystemType /@ in
},
    Proc[Labeled[Permute[{##}, invPerm] &, Labeled[Unique["\[Pi]"], Subscript["\[Pi]", Row @ ps]]], inTypes, Permute[inTypes, invPerm], "permutation"]
]


swapProc[A_, B_] := permutationProc[Cycles[{{1, 2}}], {A, B}]


cupProc[out_] := Proc[Labeled["Cup", Labeled[Unique["cup"], "\[Union]"]], {}, {reverseType @ SystemType[out], SystemType[out]}, "cup"]


capProc[in_] := ReplacePart[transposeProc @ cupProc[in], {1 -> Labeled["Cap", Labeled[Unique["cap"], "\[Intersection]"]], -1 -> "cap"}]


copyProc[in_, n_ : 2] := Proc[Labeled[{#, #} &, Labeled[Unique["copy"], "\[Gamma]"]], {SystemType[in]}, Table[SystemType[in], n], "copy"]


withTerminals[p : Proc[f_, in_, out_, ___]] := Module[{
   q,
   initial = Proc[Labeled[unWrap[{##}] &, Labeled[Unique["initial"], "\[ScriptCapitalI]"]], in, in, "initial"],
   terminal = Proc[Labeled[unWrap[{##}] &, Labeled[Unique["terminal"], "\[ScriptCapitalT]"]], out, out, "terminal"]
},
    q = If[Length @ out > 0, terminal @* p, p];
    flattenProc @ If[Length[in] > 0, q @* initial, q]
]
