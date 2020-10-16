Package["DiagramProcess`"]

PackageExport["identityProc"]
PackageExport["permutationProc"]
PackageExport["cupProc"]
PackageExport["capProc"]
PackageExport["withTerminals"]


identityProc[in_] := Proc[Identity, {SystemType @ in}, {SystemType @ in}, Labeled[Unique["\[Delta]"], "\[Delta]"]]


permutationProc[perm_Cycles, in_List] := With[{
    ps = PermutationList[perm, Length[in]],
    invPerm = InversePermutation @ perm,
    inTypes = SystemType /@ in
},
    Proc[Permute[{##}, invPerm] &, inTypes, Permute[inTypes, invPerm],
         Labeled[Unique["\[Pi]"], Subscript["\[Pi]", Row @ ps]]]
]


cupProc[out_] := Proc["\[Cup]", {}, {reverseType @ SystemType[out], SystemType[out]}, Labeled[Unique["cup"], "\[Union]"]]


capProc[in_] := Proc["\[Cap]", {SystemType[in], reverseType @ SystemType[in]}, {}, Labeled[Unique["cap"], "\[Intersection]"]]


withTerminals[p : Proc[f_, in_, out_, ___]] := Module[{
   q,
   initial = Proc[unWrap[{##}] &, in, in, Labeled[Unique["initial"], "\[ScriptCapitalI]"]],
   terminal = Proc[unWrap[{##}] &, out, out, Labeled[Unique["terminal"], "\[ScriptCapitalT]"]]
},
    q = If[Length @ out > 0, terminal @* p, p];
    flattenProc @ If[Length[in] > 0, q @* initial, q]
]
