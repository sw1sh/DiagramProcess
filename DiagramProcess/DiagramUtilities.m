Package["DiagramProcess`"]

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


Options[ArrowUp] = {"Direction" -> 1, "ArrowPosition" -> Automatic}

ArrowUp[from : {a_, b_}, to : {c_, d_}, label_, OptionsPattern[]] := {
    Arrowheads[{{
        Medium OptionValue["Direction"],
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
