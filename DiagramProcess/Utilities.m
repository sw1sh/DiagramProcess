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
PackageExport["replaceUnderHold"]
PackageExport["InteractiveGraph"]
PackageExport["Circled"]


getLabel[Labeled[_, l_]] := l

getLabel[Interpretation[l_, __]] := l

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


Options[InteractiveGraph] = DeleteDuplicatesBy[First] @ Join[Options[LocatorPane], Options[Graphics]]

Format[InteractiveGraph[g : Dynamic[data_, ops___], locopts : OptionsPattern[]], StandardForm] := DynamicModule[{
    coords, pr
},
    coords = (VertexCoordinates /. AbsoluteOptions[data, VertexCoordinates]);
    pr = Replace[OptionValue[Graphics, FilterRules[{locopts}, Options[Graphics]], PlotRange],
        {
            All | Automatic -> Dynamic[{{-.1, -.1}, {.1, .1}} + CoordinateBoundingBox[coords]],
            {ymin_ ? NumericQ, ymax_ ? NumericQ} :> Transpose[{CoordinateBounds[coords][[1]], {ymin, ymax}}],
            {x_List, y_List} :> Transpose[{x, y}]
        }];
    LocatorPane[
        Dynamic[coords, Function[Set[coords, #];
        Set[data, Graph[data, VertexCoordinates -> coords]]]],
        Graphics[Dynamic @ First[Show @ data],
        Sequence @@ FilterRules[{locopts}, Options[Graphics]]], pr,
        Sequence @@ FilterRules[{locopts, Appearance -> None}, Options[LocatorPane]]
    ]
]


Circled[expr_, opts___] := Module[{proxy, s},
    proxy = Framed[expr, ContentPadding -> False, FrameMargins -> 1];
    s = Max @ Rasterize[proxy, "RasterSize"];
    Framed[expr, opts, Alignment -> {Center, Center},
        BaselinePosition -> Baseline, ImageSize -> {s, s} / GoldenRatio,
        RoundingRadius -> Scaled[1], StripOnInput -> True
  ]
]
