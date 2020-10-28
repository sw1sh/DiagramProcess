Package["DiagramProcess`"]

PackageScope["getLabel"]
PackageScope["wrap"]
PackageScope["unWrap"]
PackageScope["enumerate"]
PackageScope["unLabel"]
PackageScope["unLabelAll"]
PackageScope["positionIn"]
PackageScope["vertexMap"]
PackageScope["edgeMap"]
PackageScope["graphReplace"]
PackageScope["replaceUnderHold"]



getLabel[Labeled[_, l_]] := l

getLabel[DirectedEdge[_, _, l_]] := l

getLabel[e : DirectedEdge[_, _]] := e

getLabel[l_] := l


unLabel[expr_] := Replace[expr, Labeled[x_, _] :> x]

unLabelAll[expr_] := expr //. Labeled[x_, _] :> x


wrap[l_List] := l

wrap[x_] := {x}


unWrap[l_List] /; Length[l] == 1 := First[l]

unWrap[x_] := x


PermutationApplied[f_, p_List] := ResourceFunction["Uncurry"][CurryApplied[f, p], Length@p]


enumerate = MapIndexed[{#1, #2[[1]]} &];


enumerateOccurrences[l_List] := Fold[SubsetMap[Range @* Length, #1, Position[##]] &, l, DeleteDuplicates[l]]


columnMap[f_, l_] := Fold[SubsetMap[f, #1, {All, #2}] &, l, Range[Min[Length /@ l]]]
columnMap[_, {}] := {}


positionIn[x_List, y_List] := With[{positions = LongestCommonSubsequencePositions[x, y]},
    If[ Length[positions] > 0,
        positions[[1, 1]],
        Infinity
    ]
]


vertexMap[f_, g_Graph] := VertexReplace[g, Map[# -> f[#] &, VertexList[g]]]

vertexMap[f_] := Function[g, vertexMap[f, g]]


edgeMap[f_, g_Graph] := EdgeAdd[EdgeDelete[g, _], Map[f[#] &, EdgeList[g]]]

edgeMap[f_] := Function[g, edgeMap[f, g]]


graphReplace[g_Graph, rules_] := edgeMap[ReplaceAll[rules], vertexMap[ReplaceAll[rules], g]]


replaceUnderHold[expr_, rule_] := With[{pos = Position[expr, First @ rule]},
    Replace[ReplacePart[expr, Thread[pos -> Map[Replace[rule], Extract[expr, pos]]]], rule]
]

replaceUnderHold[rule_] := Function[expr, replaceUnderHold[expr, rule]]

