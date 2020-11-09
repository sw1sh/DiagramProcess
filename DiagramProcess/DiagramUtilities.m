Package["DiagramProcess`"]

PackageExport["graphProc"]
PackageExport["boxNamesProc"]

PackageScope["Wire"]
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

procShape[coord_, w_, h_, OptionsPattern[]] := Module[{
    graphics, center
},
    {graphics, center} = Switch[
        OptionValue["Shape"],
        "Diamond",
        {Polygon[{{0, 0}, {w / 8, 0}, {w / 8, h / 8}, {w / 2, h / 2}, {w, 0}, {w - w / 8, 0}, {w - w / 8, - h / 8}, {w / 2, - h / 2}}], {w / 2, 0}},
        "UpTriangle",
        {Polygon[{{0, 0}, {w, 0}, {w 3 / 8, h}, {0, h 2 / 5}}], {w 3 / 8, h / 2}},
        "DownTriangle",
        {Polygon[{{0, 0}, {w, 0}, {w 3 / 8, - h}, {0, - h 2 / 5}}], {w 3 / 8, - h / 2}},
        "Rectangle",
        {Rectangle[{0, 0}, {w, h}], {w / 2, h / 2}},
        "None",
        {{}, {w / 2, h / 2}},
        "Disk",
        {Disk[{0, 0}, {w, h}], {0, 0}},
        _,
        {Polygon[{{0, 0}, {0, h}, {w, h}, {w - 1 / 4, 0}}], {w / 2, h / 2}}
    ];
    {
        EdgeForm[Black],
        Translate[graphics, coord - center]
    }
]


Options[Wire] = {"ArrowSize" -> Small, "ArrowPosition" -> Automatic,
    "Direction" -> "BottomUp",
    "VerticalShift" -> 1, "HorizontalShift" -> 1,
    "Multiply" -> 1, "MultiplyWidthIn" -> 0.1, "MultiplyWidthOut" -> 0.1,
    "Style" -> {},
    "Reverse" -> False}

Wire[from : {a_, b_}, to : {c_, d_}, label_, OptionsPattern[]] := {
    Table[
        With[{shiftIn = edgeSideShift[i, {1, 1}, OptionValue["Multiply"]] * OptionValue["MultiplyWidthIn"],
              shiftOut = edgeSideShift[If[TrueQ[OptionValue["Reverse"]], OptionValue["Multiply"] - i + 1, i], {1, 1}, OptionValue["Multiply"]] * OptionValue["MultiplyWidthOut"],
              arrowSize = OptionValue["ArrowSize"]},
        {Arrowheads[{{
            Small If[ListQ[arrowSize], arrowSize[[i]], arrowSize],
            OptionValue["ArrowPosition"] /. Automatic -> 0.4}}
        ],
        OptionValue["Style"],
        Switch[
            OptionValue["Direction"],
            "BottomUp",
            Arrow[
                BezierCurve[{
                    {a + shiftIn, b}, {a + shiftIn , (b + d) / 2},
                    {c + shiftIn, (b + d) / 2 }, {c + shiftOut, d}
                }]
            ],
            "Loop",
            Arrow[BSplineCurve[{
                from + {shiftIn, 0}, from + {shiftIn, 1}, from + {shiftIn + OptionValue["HorizontalShift"], OptionValue["VerticalShift"]},
                (from + to) / 2 + {(shiftIn + shiftOut) / 2 + OptionValue["HorizontalShift"], 0},
                to + {shiftOut + OptionValue["HorizontalShift"], - 1}, to + {shiftOut, - OptionValue["VerticalShift"]}, to + {shiftOut, 0}}
            ]],
            "DownArc",
            Arrow[BSplineCurve[{
                from + {shiftIn, 0},
                {a + shiftIn, Min[b, d] - OptionValue["VerticalShift"]},
                {(a + c) / 2, Min[b, d] - OptionValue["VerticalShift"] + (2 shiftIn (*- shiftOut*))},
                {c - shiftOut, Min[b, d] - OptionValue["VerticalShift"]},
                to - {shiftOut, 0}
            }]],
            "UpArc",
            Arrow[BSplineCurve[{
                from + {shiftIn, 0},
                {a + shiftIn, Max[b, d] + OptionValue["VerticalShift"]},
                {(a + c) / 2, Max[b, d] + OptionValue["VerticalShift"] - (2 shiftIn (*- shiftOut*))},
                {c - shiftOut, Max[b, d] + OptionValue["VerticalShift"]},
                to - {shiftOut, 0}
            }]]
        ]
        }
        ],
        {i, OptionValue["Multiply"]}
    ],
    Text[Style[label, Bold, Black, FontSize -> Small], from + {2 Boole[a >= c] - 1, 1} / 8]
}


edgeSideShift[i_, {w_ ? NumericQ, _}, arity_] := Max[w - 1, 1 / 2] / Max[arity - 1, 1] * ((i - 1) - (arity - 1) / 2)


betweenEdges[p : Proc[f_, pIn_, pOut_, ___], q : Proc[g_, qIn_, qOut_, ___]] := With[{
    in = Catenate[enumerate @* Thread /@ procIn[p]],
    out = Catenate[enumerate @* Thread /@ procOut[q]]
},
    If[ Length[in] == 0 || Length[out] == 0,
        {},
        MapThread[DirectedEdge[#1[[1, 1]], #2[[1, 1]], #1[[2]] -> #2[[2]]] &, {out, in}]
    ]
]


rescaleProc[p_Proc, graph_Graph, scale_] := With[{
    esIn = EdgeList[graph, DirectedEdge[_, p, ___]],
    esOut = EdgeList[graph, DirectedEdge[p, _, ___]],
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
