Package["DiagramProcess`"]

PackageExport["identityProc"]
PackageExport["permutationProc"]
PackageExport["swapProc"]
PackageExport["cupProc"]
PackageExport["capProc"]
PackageExport["withTerminals"]


identityProc[in_] := Proc[Identity, {SystemType @ in}, {SystemType @ in}, Labeled[Unique["\[Delta]"], "\[Delta]"], "id"]


permutationProc[perm_Cycles, in_List] := With[{
    ps = PermutationList[perm, Length[in]],
    invPerm = InversePermutation @ perm,
    inTypes = SystemType /@ in
},
    Proc[Permute[{##}, invPerm] &, inTypes, Permute[inTypes, invPerm],
         Labeled[Unique["\[Pi]"], Subscript["\[Pi]", Row @ ps]], "permutation"]
]


swapProc[A_, B_] := permutationProc[Cycles[{{1, 2}}], {A, B}]


cupProc[out_] := Proc["\[Cup]", {}, {reverseType @ SystemType[out], SystemType[out]}, Labeled[Unique["cup"], "\[Union]"], "cup"]


capProc[in_] := ReplacePart[transposeProc @ cupProc[in], {4 -> Labeled[Unique["cap"], "\[Intersection]"], 5 -> "cap"}]


withTerminals[p : Proc[f_, in_, out_, ___]] := Module[{
   q,
   initial = Proc[unWrap[{##}] &, in, in, Labeled[Unique["initial"], "\[ScriptCapitalI]"], "initial"],
   terminal = Proc[unWrap[{##}] &, out, out, Labeled[Unique["terminal"], "\[ScriptCapitalT]"], "terminal"]
},
    q = If[Length @ out > 0, terminal @* p, p];
    flattenProc @ If[Length[in] > 0, q @* initial, q]
]
