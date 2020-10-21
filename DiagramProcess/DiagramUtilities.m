Package["DiagramProcess`"]

PackageExport["graphProc"]
PackageExport["boxNamesProc"]

PackageScope["ArrowUp"]
PackageScope["procShape"]
PackageScope["edgeSideShift"]
PackageScope["rescaleProc"]
PackageScope["betweenEdges"]
PackageScope["graphVertexCoordinates"]
PackageScope["graphBox"]
PackageScope["graphSize"]
PackageScope["graphCenter"]
PackageScope["scaleVertices"]
PackageScope["shiftVertices"]



graphVertexCoordinates[g_Graph] := AssociationThread[VertexList[g] -> AnnotationValue[g, VertexCoordinates]]


graphBox[g_Graph] := With[{
    vertexSizes = AnnotationValue[g, VertexSize],
    vertexCoordinates = graphVertexCoordinates[g]},
    {
        MapThread[Min, Values @ Merge[{vertexCoordinates, vertexSizes}, #[[1]] - #[[2]] / 2 &]],
        MapThread[Max, Values @ Merge[{vertexCoordinates, vertexSizes}, #[[1]] + #[[2]] / 2 &]]
    }
]


graphSize[g_Graph] := ReverseApplied[Subtract] @@ graphBox[g]


graphCenter[g_Graph] := Mean /@ Transpose[graphBox[g]]


scaleVertices[g_Graph, scale_] := Annotate[g, VertexSize -> MapAt[# * scale &, AnnotationValue[g, VertexSize], {All, 2}]]


shiftVertices[g_Graph, shift_] := Annotate[g, VertexCoordinates -> Normal @ Map[# + shift &, graphVertexCoordinates[g]]]


positionIn[x_List, y_List] := With[{positions = LongestCommonSubsequencePositions[x, y]},
    If[ Length[positions] > 0,
        positions[[1, 1]],
        Infinity
    ]
]

graphProc[g_Graph] := Module[{
   bottomLayer,
   restGraph
},
    bottomLayer = Select[VertexList[g], VertexInDegree[g, #] == 0 &];
    restGraph = VertexDelete[g, bottomLayer];
    If[ VertexCount[restGraph] > 0,
        With[{proc = graphProc[restGraph]}, proc @* Apply[CircleTimes, SortBy[bottomLayer, positionIn[proc[[2]], #[[3]]] &]]],
        Apply[CircleTimes, bottomLayer]
    ]
]

stripTypeSubsripts[SystemType[t_, args___]] := SystemType[Replace[t, Subscript[x_, _] :> x], args]
stripTypeSubsripts[p_Proc] := MapAt[Map[stripTypeSubsripts], p, {{2}, {3}}]

removeCycles[g_Graph] := Module[{
    loops, cycles, counts
},
    loops = EdgeList[g, DirectedEdge[x_, x_, ___]];
    cycles = FindCycle[EdgeDelete[g, loops], Infinity, All];
    counts = Counts[Catenate @ cycles];
    Join[loops, DeleteDuplicates[First @* MaximalBy[counts] /@ cycles]]
]

boxNamesProc[boxes_List] := Module[{procs, ins, outs, edges, graph},
    procs = Proc /@ boxes;
    ins = #[[2]] & /@ procs;
    outs = #[[3]] & /@ procs;
    edges = Catenate @ MapIndexed[
        Function[With[{pos = FirstPosition[outs, #1]},
            If[ ! MissingQ[pos],
                With[{from = procs[[pos[[1]]]], to = procs[[#2[[1]]]], i = pos[[2]], j = #2[[2]], type = #1},
                    (*If[ pos[[1]] === #2[[1]],
                        EdgeList @ ProcGraph[traceProc[stripSubsripts @ from, j, i]],
                        stripSubsripts @ DirectedEdge[from, to, {i -> j, type}]
                    ]*)
                    DirectedEdge[stripTypeSubsripts @ from, stripTypeSubsripts @ to, {i -> j, type}]
                ],
                Nothing
            ]
        ]],
        ins,
        {2}
    ];
    graph = Graph[Union[stripTypeSubsripts /@ procs, VertexList[edges]], edges];
    cycleEdges = removeCycles[graph];
    cyclessProc = graphProc @ EdgeDelete[graph, cycleEdges];
    Fold[traceProc[#1, #2[[3, 1, 1]], #2[[3, 1, 2]]] &, cyclessProc, cycleEdges]
]


Options[procShape] = {"Shape" -> "Trapezoid"}

procShape[coord_, w_, h_, OptionsPattern[]] := {
    FaceForm[White], EdgeForm[Black],
    Translate[
        Switch[OptionValue["Shape"],
            "Diamond",
            Polygon[{{w / 2, 0}, {w, h / 2}, {w / 2, h}, {0, h / 2}}],
            "UpTriangle",
            Polygon[{{0, 0}, {w, 0}, {w / 2, h}, {0, h / 2}}],
            "DownTriangle",
            Polygon[{{0, h}, {w, h}, {w / 2, 0}, {0, h / 2}}],
            _,
            Polygon[{{0, 0}, {0, h}, {w, h}, {w - 1 / 4, 0}}]
        ],
        coord - {w / 2, h / 2}
    ]
}


Options[ArrowUp] = {"ArrowSize" -> 1, "ArrowPosition" -> Automatic}

ArrowUp[from : {a_, b_}, to : {c_, d_}, label_, OptionsPattern[]] := {
    Arrowheads[{{
        Small Sign[OptionValue["ArrowSize"]],
        OptionValue["ArrowPosition"] /. Automatic -> 0.4}}
    ],
    Arrow[
        BezierCurve[{{a, b}, {a, (b + d) / 2}, {c, (b + d) / 2}, {c, d}}]
    ],
    Text[Style[label, Bold, Black], from + {2 Boole[a >= c] - 1, 1} / 8]
}


edgeSideShift[i_, {w_, _}, arity_] := Max[w - 1, 1 / 2] / Max[arity - 1, 1] * ((i - 1) - (arity - 1) / 2)


betweenEdges[p : Proc[f_, pIn_, pOut_, ___], q : Proc[g_, qIn_, qOut_, ___]] := With[{
    in = Catenate[enumerate @* Thread /@ procIn[p]],
    out = Catenate[enumerate @* Thread /@ procOut[q]]
},
    If[ Length[in] == 0 || Length[out] == 0,
        {},
        MapThread[DirectedEdge[#1[[1, 1]], #2[[1, 1]], {#1[[2]] -> #2[[2]], #1[[1, 2]]}] &, {out, in}]
    ]
]


rescaleProc[p_Proc, graph_Graph, scale_] := With[{
    esIn = EdgeList[graph, DirectedEdge[_, p, ___]],
    esOut = EdgeList[graph, DirectedEdge[p, _, ___]],
    (*coord = AnnotationValue[{graph, p}, VertexCoordinates],*)
    size = AnnotationValue[{graph, p}, VertexSize]},
    Fold[Function[{g, ej},
        Annotate[{g, ej[[1]]},
            EdgeShapeFunction ->
            Function[
                AnnotationValue[{g, ej[[1]]}, EdgeShapeFunction][
                    MapAt[# + {- edgeSideShift[ej[[2]], size, Length @ esOut] + edgeSideShift[ej[[2]], scale * size, Length @ esOut], 0} &,
                          #1, 1], #2]
            ]
        ]
    ],
    Fold[Function[{g, ei},
        Annotate[{g, ei[[1]]},
            EdgeShapeFunction ->
            Function[
                AnnotationValue[{g, ei[[1]]}, EdgeShapeFunction][
                    MapAt[# + {- edgeSideShift[ei[[2]], size, Length @ esIn] + edgeSideShift[ei[[2]], scale * size, Length @ esIn], 0} &,
                          #1, -1], #2]
            ]
        ]
    ],
    Annotate[{graph, p}, VertexSize -> scale * size], enumerate @ esIn
    ],
    enumerate @ esOut
   ]
]
