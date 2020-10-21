Package["DiagramProcess`"]

PackageExport["ProcGraph"]


Options[ProcGraph] = {
    "ComposeDistance" -> Automatic,
    "ParallelComposeDistance" -> Automatic,
    "AddTerminals" -> False,
    "OutlineProcess" -> False, "ShowLabels" -> True,
    "ArrowPosition" -> Automatic,
    "Size" -> Automatic};


ProcGraph[p : Proc[f_, in_, out_, ___], opts : OptionsPattern[]] := Module[{},
    If[TrueQ[OptionValue["AddTerminals"]],
        Return @ ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];
    Graph[{Annotation[p, {
        VertexCoordinates -> {0, 0},
        VertexSize -> MapAt[Min[Replace[#, Automatic -> 1], 1] & ,
            MapAt[Replace[Automatic -> Max[procArity[p], 1]], Replace[OptionValue["Size"], Automatic -> {Automatic, Automatic}], 1],
            2
        ],
        VertexShapeFunction ->
            Module[{
                inArity = Length[in], outArity = Length[out],
                tag = procTag[p],
                label = If[TrueQ @ OptionValue["ShowLabels"], getLabel[p], ""],
                arrowPos = OptionValue["ArrowPosition"] /. Automatic -> 0.5,
                shape = Which[
                    procArity[p] == 0,
                    "Diamond",
                    procInArity[p] == 0,
                    "DownTriangle",
                    procOutArity[p] == 0,
                    "UpTriangle",
                    True,
                    "Trapezoid"
                ],
                shapeFun,
                outlineShapeFun
            },
            outlineShapeFun = procShape[#1, #3[[1]], #3[[2]], "Shape" -> shape] &;

            shapeFun = Which[
                MatchQ[tag, "id" | "cast"],
                Function @ With[{dir = 1 - 2 Boole @ backwardTypeQ[#2[[2, 1]]]},
                    {
                        Black,
                        ArrowUp[#1 + {0, - 1 / 2}, #1 + {0, 1 / 2}, "",
                            "ArrowSize" -> 0 * dir, "ArrowPosition" -> arrowPos]
                    }
                ],

                MatchQ[tag, "initial" | "terminal"],
                {} &,

                MatchQ[tag, "permutation"],
                With[{xs = Range @ Length @ in},

                    Function[{coord, v, size},
                        MapThread[Function[{fromIndex, toIndex}, With[{
                            fromShift = {edgeSideShift[fromIndex, size, inArity], - 1 / 2},
                            toShift = {edgeSideShift[toIndex, size, outArity], 1 / 2},
                            dir = 1 - 2 Boole @ backwardTypeQ[v[[2, fromIndex]]]
                        },
                        {
                            Black,
                            ArrowUp[coord + fromShift, coord + toShift, "",
                                "ArrowSize" -> 0 * dir, "ArrowPosition" -> arrowPos / 2]
                        }
                        ]
                        ], {p @@ xs, xs}]
                    ]
                ],

                MatchQ[tag, "cup" | "cap"],
                Function[{coord, v, size}, If[Length[in] == 0, {
                    (*Arrowheads[{{Medium (2 Boole[backwardTypeQ @ out[[1]]] - 1), arrowPos}}],*)
                    Black,
                    BezierCurve @ {
                        coord + {edgeSideShift[1, size, 2], 1 / 2},
                        coord + {edgeSideShift[1, size, 2], 0},
                        coord + {edgeSideShift[2, size, 2], 0},
                        coord + {edgeSideShift[2, size, 2], 1 / 2}
                        }
                }, {
                    (*Arrowheads[{{Medium (1 - 2 Boole[backwardTypeQ @ in[[1]]]), arrowPos}}],*)
                    Black,
                    BezierCurve @ {
                        coord + {edgeSideShift[1, size, 2], - 1 / 2},
                        coord + {edgeSideShift[1, size, 2], 0},
                        coord + {edgeSideShift[2, size, 2], 0}, 
                        coord + {edgeSideShift[2, size, 2], - 1 / 2}
                    }
                }]],

                MatchQ[tag, "copy"],
                Function[{coord, v, size}, {
                    Black,
                    Table[
                        ArrowUp[coord + {0, - 1 / 2}, coord + {edgeSideShift[i, size, outArity], 1 / 2}, "",
                                "ArrowPosition" -> arrowPos],
                        {i, Length @ out}
                    ]
                }],

                True,
                If[ MatchQ[label, _Transpose],
                    With[{fun = outlineShapeFun},
                        GeometricTransformation[fun[##], RotationTransform[Pi, #1]] &
                    ],
                    outlineShapeFun
                ]
            ];
            With[{fun = shapeFun},
                If[TrueQ[OptionValue["OutlineProcess"]],
                    shapeFun = Function[{fun[##],
                        FaceForm[Transparent], EdgeForm[Dashed],
                        outlineShapeFun[##]
                    }]
                ]
            ];
            With[{fun = shapeFun},
                If[! MatchQ[tag, "cap" | "cup" | "initial" | "terminal" | "id" | "cast" | "permutation" | "copy"],
                    shapeFun = {
                        fun[##],
                        Text[Style[label, FontSize -> 16],
                            #1 + {0, 0(*Switch[shape, "UpTriangle", - #3[[2]] / 4, "DownTriangle", #3[[2]] / 4, _, 0]*)}, Center]
                    } &
                ]
            ];

            shapeFun
         ]
      }
    ]},
    (* edges *)
    {}
    ]
]


ProcGraph[Proc[f : _Composition | _CircleTimes | _Transpose, args__], opts : OptionsPattern[]] :=
    ProcGraph[Proc[Defer[f], args], opts]


ProcGraph[p : Proc[Defer[CircleTimes[ps__Proc]], in_, out_, ___], opts : OptionsPattern[]] := Module[{
    graphs, size,
    graphWidths, graphHeights,
    wideProcPositions, qs,
    parallelComposeDistance,
    vertices, edges,
    vertexSize, vertexCoordinates,
    vertexXShifts, vertexYShifts, vertexCoordinateShifts,
    shiftedGraphs, newVertexCoordinates
},
    If[TrueQ[OptionValue["AddTerminals"]],
        Return @ ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];
    size = Replace[OptionValue["Size"], Automatic -> {Automatic, Automatic}];
    graphs = Map[ProcGraph[#, "AddTerminals" -> False, "Size" -> {Automatic, size[[2]]}, opts] &, {ps}];
    {graphWidths, graphHeights} = Transpose[graphSize /@ graphs];
    wideProcPositions = Map[procArity[#] > 1 &, {ps}];
    qs = Pick[{ps}, wideProcPositions];
    With[{
        scaleWidth = If[size[[1]] =!= Automatic && Length[qs] > 0,
            (size[[1]] - (Length[{ps}] - Length[qs]) - (Length[{ps}] - 1) * Replace[OptionValue["ParallelComposeDistance"], Automatic -> 1]) / Total[Pick[graphWidths, wideProcPositions]],
            1
        ]
    },
        graphs = MapThread[ProcGraph[#1, "AddTerminals" -> False, "Size" -> {#2 * If[#3 > 1, scaleWidth, 1], Max[graphHeights]}, opts] &,
            {{ps}, graphWidths, procArity /@ {ps}}
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
    shiftedGraphs = MapThread[shiftVertices, {graphs, vertexCoordinateShifts}];
    shiftedGraphs = MapThread[shiftVertices[#1, {0, #2[[2]]}] &, {shiftedGraphs, Minus @* graphCenter /@ shiftedGraphs}];
    newVertexCoordinates = Association[graphVertexCoordinates /@ shiftedGraphs];

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
        graphs = Map[ProcGraph[#, "AddTerminals" -> False, "ParallelComposeDistance" -> Automatic,
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
                    label = If[TrueQ[OptionValue["ShowLabels"]] && Not[MatchQ[procTag[v], "id"]], Last @ getLabel[e], ""],
                    pos = OptionValue["ArrowPosition"]
                },
                e -> Function[
                    {
                        Black,
                        ArrowUp[#1[[1]] + fromShift, #1[[-1]] + toShift, label,
                            "ArrowSize" -> dir, "ArrowPosition" -> pos]
                    }
                ]
                ]
            ]],
            allEdges
        ]
   ]
]
