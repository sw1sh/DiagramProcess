Package["DiagramProcess`"]

PackageScope["ArrowUp"]
PackageScope["procShape"]
PackageScope["edgeSideShift"]
PackageScope["rescaleProc"]
PackageScope["betweenEdges"]


procShape[coord_, v_, a_, b_, h_] := With[{c = If[a == b, a - 1 / 4, a]}, {
    FaceForm[White], EdgeForm[Black],
    Translate[
        ResourceFunction["Trapezoid"][c, 90 Degree, b, ArcTan[b - c, h]],
        coord - {b / 2, h / 2}
    ],
    Text[Style[v, FontSize -> 16], coord, Center]
}]


Options[ArrowUp] = {"Direction" -> 1, "ArrowPosition" -> Automatic}

ArrowUp[from : {a_, b_}, to : {c_, d_}, label_, OptionsPattern[]] := {
    Arrowheads[{{
        Medium OptionValue["Direction"],
        OptionValue["ArrowPosition"] /. Automatic -> 0.4}}
    ],
    Arrow[
        BezierCurve[{{a, b}, {a, (b + d) / 2}, {c, (b + d) / 2}, {c, d}}]
    ],
    Text[Style[label, Bold, Black], from + {2 Boole[a >= c] - 1, 1} (d - b) / 8]
}


edgeSideShift[i_, {w_, _}, arity_] := Max[w - 1, 1 / 2] / Max[arity - 1, 1] * ((i - 1) - (arity - 1) / 2)


betweenEdges[p : Proc[f_, pIn_, pOut_, ___], q : Proc[g_, qIn_, qOut_, ___]] := With[{
    in = Catenate[enumerate @* Thread /@ procIn[p]],
    out = Catenate[enumerate @* Thread /@ procOut[q]]
},
    MapThread[DirectedEdge[#1[[1, 1]], #2[[1, 1]], {#1[[2]] -> #2[[2]], #1[[1, 2]]}] &, {out, in}]
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
