Package["DiagramProcess`"]

PackageExport["ProcGraph"]


Options[ProcGraph] = {
    "ComposeDistance" -> Automatic,
    "ParallelComposeDistance" -> Automatic, "AddTerminals" -> False,
    "OutlineProcess" -> False, "ShowLabels" -> True,
    "ArrowPosition" -> Automatic,
    "Size" -> Automatic};

ProcGraph[p : Proc[f_, in_, out_, ___], opts : OptionsPattern[]] := Module[{},
    If[TrueQ[OptionValue["AddTerminals"]],
        Return@ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];

    Graph[{Annotation[p, {
        VertexCoordinates -> {0, 0},
        VertexSize -> MapAt[Replace[Automatic -> 1],
            MapAt[Replace[Automatic -> procArity[p]], Replace[OptionValue["Size"], Automatic -> {Automatic, Automatic}], 1],
            2
        ],
        VertexShapeFunction ->
            With[{
                inArity = Length[in], outArity = Length[out],
                name = getLabel[p],
                label = If[TrueQ @ OptionValue["ShowLabels"], getLabel[p], ""],
                arrowPos = OptionValue["ArrowPosition"] /. Automatic -> 0.25
            },
            With[{shapeFun = Which[
                MatchQ[name, "\[Delta]"],
                Function @ With[{dir = 1 - 2 Boole @ backwardTypeQ[#2[[2, 1]]]},

                    ArrowUp[#1 + {0, - 1 / 2}, #1 + {0, 1 / 2}, "", 
                            "Direction" -> dir, "ArrowPosition" -> arrowPos]
                ],

                MatchQ[name, "\[ScriptCapitalT]" | "\[ScriptCapitalI]"],
                {} &,

                MatchQ[name, Subscript["\[Pi]", __]],
                With[{xs = Range @ Length @ in},

                    Function[{coord, v, size},
                        MapThread[Function[{fromIndex, toIndex}, With[{
                            fromShift = {edgeSideShift[fromIndex, size, inArity], - 1 / 2},
                            toShift = {edgeSideShift[toIndex, size, outArity], 1 / 2},
                            dir = 1 - 2 Boole @ backwardTypeQ[v[[2, fromIndex]]]
                        },
                        ArrowUp[coord + fromShift, coord + toShift, "",
                                "Direction" -> dir, "ArrowPosition" -> arrowPos]
                        ]
                        ], {p @@ xs, xs}]
                    ]
                ],

                MatchQ[name, "\[Union]"] && ! transposeQ[p] || MatchQ[name, "\[Intersection]"] && transposeQ[p],
                Function[{coord, v, size}, {
                    Arrowheads[{{Medium (2 Boole[backwardTypeQ @ out[[1]]] - 1), arrowPos}}],

                    Arrow[BezierCurve @ {
                        coord + {edgeSideShift[1, size, 2], 1 / 2},
                        coord + {edgeSideShift[1, size, 2], 0},
                        coord + {edgeSideShift[2, size, 2], 0},
                        coord + {edgeSideShift[2, size, 2], 1 / 2}
                        }
                    ]
                }],

                MatchQ[name, "\[Intersection]"] && ! transposeQ[p] || MatchQ[name, "\[Union]"] && transposeQ[p],
                Function[{coord, v, size}, {
                    Arrowheads[{{Medium (1 - 2 Boole[backwardTypeQ@in[[1]]]), arrowPos}}],

                    Arrow[BezierCurve @ {
                        coord + {edgeSideShift[1, size, 2], - 1 / 2},
                        coord + {edgeSideShift[1, size, 2], 0},
                        coord + {edgeSideShift[2, size, 2], 0}, 
                        coord + {edgeSideShift[2, size, 2], - 1 / 2}
                    }]
                }],

                True,
                procShape[#1, label, #3[[1]], #3[[1]], #3[[2]]] &
            ]},
            If[TrueQ[OptionValue["OutlineProcess"]],
            {
                shapeFun[##],
                FaceForm[Transparent], EdgeForm[Dashed],
                procShape[#1, "", #3[[1]], #3[[1]], #3[[2]]]
            } &,
            shapeFun[##] &
            ]
         ]]
      }
    ]},
    (* edges *)
    {}
    ]
]

ProcGraph[Proc[f : _Composition | _CircleTimes, args__], opts : OptionsPattern[]] :=
    ProcGraph[Proc[Defer[f], args], opts]


ProcGraph[p : Proc[Defer[CircleTimes[ps__Proc]], in_, out_, ___], opts : OptionsPattern[]] := Module[{
    graphs, size,
    graphWidths, graphHeights,
    parallelComposeDistance,
    vertices, edges,
    vertexSize, vertexCoordinates,
    vertexXShifts, vertexYShifts, vertexCoordinateShifts,
    newVertexCoordinates
},
    If[TrueQ[OptionValue["AddTerminals"]],
        Return @ ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];
    size = Replace[OptionValue["Size"], Automatic -> {Automatic, Automatic}];
    graphs = Map[ProcGraph[#, "AddTerminals" -> False, "Size" -> {Automatic, size[[2]]}, opts] &, {ps}];
    {graphWidths, graphHeights} = Transpose[graphSize /@ graphs];
    With[{
        scaleWidth = If[size[[1]] =!= Automatic && OptionValue["ParallelComposeDistance"] =!= Automatic,
            (size[[1]] - (Length[{ps}] - 1) * OptionValue["ParallelComposeDistance"]) / Total[graphWidths],
            1
        ]
    },
        graphs = MapThread[ProcGraph[#1, "AddTerminals" -> False, "Size" -> {#2 * scaleWidth, Max[graphHeights]}, opts] &,
            {{ps}, graphWidths}
        ];
        {graphWidths, graphHeights} = Transpose[graphSize /@ graphs];
    ];
    parallelComposeDistance = Replace[OptionValue["ParallelComposeDistance"], Automatic -> If[size[[1]] =!= Automatic,
        Max[(size[[1]] - Total[graphWidths]) / (Length[{ps}] - 1), 0],
        1
    ]];
    vertices = VertexList /@ graphs;
    edges = Catenate[EdgeList /@ graphs];
    vertexSize = AnnotationValue[#, VertexSize] & /@ graphs;
    vertexCoordinates = AnnotationValue[#, VertexCoordinates] & /@ graphs;
    vertexXShifts = FoldList[
        #1 + #2 + parallelComposeDistance &,
        0,
        Map[Mean, Partition[graphWidths, 2, 1]]
    ];
    vertexYShifts = Map[- Mean[#] &, vertexCoordinates[[All, All, 2]]];
    vertexCoordinateShifts = Thread[{vertexXShifts, vertexYShifts}];

    newVertexCoordinates = Association @ Catenate @ MapThread[
        Function[{vs, coords, shift},
            MapThread[#1 -> #2 + shift &, {vs, coords}]
        ],
        {vertices, vertexCoordinates, vertexCoordinateShifts}
    ];

    Graph[Catenate @ vertices, edges,
        VertexCoordinates -> newVertexCoordinates,
        VertexSize -> Catenate @ vertexSize,
        VertexShapeFunction -> Catenate[AnnotationValue[#, VertexShapeFunction] & /@ graphs],
        EdgeShapeFunction -> Catenate[Replace[AnnotationValue[#, EdgeShapeFunction], Automatic -> {}] & /@ graphs]
    ]
]

ProcGraph[p : Proc[Defer[Composition[ps__Proc]], in_, out_, ___], opts : OptionsPattern[]] := Module[{
    graphs, size,
    composeDistance,
    vertices, edges,
    graphWidths, graphHeights,
    vertexSize, vertexCoordinates,
    inBetweenEdges, allEdges,
    outArities, inArities,
    vertexXShifts, vertexYShifts, vertexCoordinateShifts,
    shiftedGraphs,
    newVertexCoordinates, newVertexSize
},
    If[TrueQ[OptionValue["AddTerminals"]], 
        Return @ ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];
    size = Replace[OptionValue["Size"], Automatic -> {Automatic, Automatic}];
    graphs = Map[ProcGraph[#, "AddTerminals" -> False, "Size" -> {size[[1]], Automatic}, opts] &, {ps}];
    {graphWidths, graphHeights} = Transpose[graphSize /@ graphs];
    If[size[[1]] === Automatic,
        graphs = Map[ProcGraph[#, "AddTerminals" -> False,
        "Size" -> {Max[graphWidths], size[[2]]}, opts] &, {ps}];
        {graphWidths, graphHeights} = Transpose[graphSize /@ graphs];
    ];
    composeDistance = If[size[[2]] === Automatic,
        Replace[OptionValue["ComposeDistance"], Automatic -> 1],
        Max[(size[[2]] - Total[graphHeights]) / (Length[{ps}] - 1), 0]
    ];
    vertices = VertexList /@ graphs;
    edges = Catenate[EdgeList /@ graphs];
    vertexSize = AnnotationValue[#, VertexSize] & /@ graphs;
    vertexCoordinates = AnnotationValue[#, VertexCoordinates] & /@ graphs;
    vertexXShifts = Map[- Mean[#] &, vertexCoordinates[[All, All, 1]]];
    vertexYShifts = FoldList[
        #1 - #2 - composeDistance &,
        0,
        Map[Mean, Partition[graphHeights, 2, 1]]
    ];
    vertexCoordinateShifts = Thread[{vertexXShifts, vertexYShifts}];
    inBetweenEdges = Catenate[Apply[betweenEdges] /@ Partition[{ps}, 2, 1]];
    allEdges = Join[edges, inBetweenEdges];
    outArities = GroupBy[allEdges, First, Length];
    inArities = GroupBy[allEdges, #[[2]] &, Length];
    shiftedGraphs = MapThread[shiftVertices, {graphs, vertexCoordinateShifts}];
    shiftedGraphs = MapThread[shiftVertices[#1, {#2[[1]], 0}] &, {shiftedGraphs, Minus @* graphCenter /@ shiftedGraphs}];
    newVertexCoordinates = Association[graphVertexCoordinates /@ shiftedGraphs];
    newVertexSize = Association @ vertexSize;
    Graph[Catenate @ vertices, allEdges,
        VertexCoordinates -> Normal @ newVertexCoordinates,
        VertexSize -> Normal @ newVertexSize,
        VertexShapeFunction -> Catenate @ Map[AnnotationValue[#, VertexShapeFunction] &, graphs],
        EdgeShapeFunction -> Map[Function[e,
            With[{i = e[[-1, 1, 1]], j = e[[-1, 1, 2]], v = e[[1]], w = e[[2]]},
                With[{
                    fromShift = {edgeSideShift[i, newVertexSize[v], outArities[v]], 1 / 2},
                    toShift = {edgeSideShift[j, newVertexSize[w], inArities[w]], - 1 / 2},
                    dir = 1 - 2 Boole @ OptionValue[SystemType, Options[v[[3, i]]], "Backward"],
                    label = If[TrueQ @ OptionValue["ShowLabels"], Last @ getLabel[e], ""],
                    pos = OptionValue["ArrowPosition"]
                },
                e -> Function[
                    ArrowUp[#1[[1]] + fromShift, #1[[-1]] + toShift, label,
                            "Direction" -> dir, "ArrowPosition" -> pos]
                ]
                ]
            ]],
            allEdges
        ]
   ]
]
