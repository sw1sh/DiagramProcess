Package["DiagramProcess`"]

PackageScope["getLabel"]
PackageScope["wrap"]
PackageScope["enumerate"]
PackageScope["unLabel"]


getLabel[Proc[_, _, _, l_, ___]] := getLabel[l]
getLabel[Labeled[_, l_]] := l
getLabel[DirectedEdge[_, _, l_]] := l
getLabel[e : DirectedEdge[_, _]] := e
getLabel[l_] := l


unLabel[expr_] := expr //. Labeled[x_, _] :> x


wrap[l_List] := l
wrap[x_] := {x}


unWrap[l_List] /; Length[l] == 1 := First[l]
unWrap[x_] := x


PermutationApplied[f_, p_List] := ResourceFunction["Uncurry"][CurryApplied[f, p], Length@p]


enumerate = MapIndexed[{#1, #2[[1]]} &];


enumerateOccurrences[l_List] := Fold[SubsetMap[Range @* Length, #1, Position[##]] &, l, DeleteDuplicates[l]]


columnMap[f_, l_] := Fold[SubsetMap[f, #1, {All, #2}] &, l, Range[Min[Length /@ l]]]
columnMap[_, {}] := {}
