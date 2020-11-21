Package["DiagramProcess`"]

PackageExport["ProcGraph"]
PackageExport["simplifyProcGraph"]


Options[ProcGraph] = {
    "ComposeDistance" -> Automatic,
    "ParallelComposeDistance" -> Automatic,
    "CircuitDistance" -> 1,
    "ProductWidth" -> Automatic,
    "AddTerminals" -> False,
    "Outline" -> False,
    "ShowArrowLabels" -> False,
    "ShowProcessLabels" -> True,
    "ShowWireLabels" -> True,
    "ShowProcessArrows" -> False,
    "ArrowPosition" -> Automatic,
    "Size" -> Automatic,
    "ThickDoubleWire" -> False,
    "ShowComposites" -> False,
    "Interactive" -> False
};



ProcGraph[p_Proc, opts : OptionsPattern[]] /; TrueQ[OptionValue[ProcGraph, {opts}, "Interactive"]] :=
    InteractiveGraph @ ProcGraph[p, "Interactive" -> False, opts]


ProcGraph[p : Proc[Except[Labeled[Defer[_Plus], _] | Defer[_Plus]], ___], opts : OptionsPattern[]] /; TrueQ[OptionValue[ProcGraph, {opts}, "AddTerminals"]] :=
    ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]


ProcGraph[p : (Proc[Except[_Defer | Labeled[_Defer, _]], ___] | _Proc ? (procTagQ["double" | "composite"])), opts : OptionsPattern[]] := Module[{
    q, in, out, vertexSize, vertexCoords, vertexLabel, graph = None
},
    q = p;
    If[ procTagQ[q, "transpose"],
        q = transposeProc[q]
    ];
    If[ procTagQ[q, "adjoint"],
        q = adjointProc[q]
    ];
    in = procInput[q]; out = procOutput[q];
    vertexLabel = If[TrueQ[OptionValue["ShowProcessLabels"]], stripProcLabel @ procLabel[p], ""];
    vertexCoords = {0, 0};
    vertexSize = MapAt[Min[Replace[#, Automatic -> 1], 1] & ,
        MapAt[Replace[Automatic -> Max[procArity[p], 1]], Replace[OptionValue["Size"], Automatic -> {Automatic, Automatic}], 1],
        2
    ];
    If[ procTagQ[p, "initial" | "terminal"],
        vertexCoords = vertexCoords + If[procTagQ[p, "initial"], {0, vertexSize[[2]] / 2}, {0, - vertexSize[[2]] / 2}];
        vertexSize = vertexSize {1, 0}
    ];
    If[ procTagQ[p, "composite"] && TrueQ[OptionValue["ShowComposites"]],
        graph = ProcGraph[unCompositeProc[q], "AddTerminals" -> True, opts];
        vertexLabel = "";
        vertexSize = graphSize[graph];
        vertexCoords = graphCenter[graph];
    ];
    If[ procTagQ[p, "spider"],
        vertexSize = If[ procTagQ[p, "topological"], {1 / 4, 1 / 4}, {1 / 2, 1 / 2}]
    ];
    Graph[{Annotation[p, {
        VertexCoordinates -> vertexCoords,
        VertexSize -> vertexSize,
        VertexLabels -> If[! unlabeledProcQ[p], Placed[vertexLabel, Center], None],
        VertexShapeFunction -> Module[{shapeFun, outlineShapeFun}, With[{
                pIn = procInput[p, True], pOut = procOutput[p, True],
                qIn = procInput[q, True], qOut = procOutput[q, True],
                pInArity = procInArity[p, True], pOutArity = procOutArity[p, True],
                qInArity = procInArity[q, True], qOutArity = procOutArity[q, True],
                inArity = Length[in], outArity = Length[out],
                productWidth = OptionValue["ProductWidth"] /. Automatic -> 1 / 10,
                arrowPos = OptionValue["ArrowPosition"] /. Automatic -> 0.5,
                shape = Which[
                    procTagQ[q, "zero"],
                    "None",
                    procTagQ[q, "spider"],
                    "Disk",
                    procArity[q] == 0,
                    "Diamond",
                    procInArity[q] == 0,
                    "DownTriangle",
                    procOutArity[q] == 0,
                    "UpTriangle",
                    True,
                    "Trapezoid"
                ],
                posScale = With[{size = vertexSize}, If[procTagQ[q, "spider"], #1 + Normalize[#2] size / 2, #1 + #2] &]
        },
        outlineShapeFun = procShape[#1, #3[[1]], #3[[2]], "Shape" -> shape] &;

        If[ procTagQ[q, "composite"] && TrueQ[OptionValue["ShowComposites"]],
            With[{graphics = First[GraphPlot[graph]]},
                shapeFun = GeometricTransformation[graphics, TranslationTransform[#1 - vertexCoords]] &
            ],

            shapeFun = Which[
                procTagQ[q, "id" | "cast"],
                With[{dir = (1 - 2 Boole @ dualTypesQ[First @ If[procTagQ[q, "spider"], in, pIn]]) Boole[TrueQ[OptionValue["ShowProcessArrows"]]],
                      multiply = With[{arity = typeArity[First @ If[procTagQ[q, "spider"], in, pIn]]}, If[TrueQ[OptionValue["ThickDoubleWire"]] && arity == 2, 1, arity]],
                      style = If[TrueQ[OptionValue["ThickDoubleWire"]] && typeArity[First @ If[procTagQ[q, "spider"], in, pIn]] == 2, Thickness[Large], Thickness[Medium]]},
                    Function @ {
                        Black,
                        Wire[Sequence @@ If[procTagQ[p, "circuit"] && (typeArity[pIn[[1]]] typeArity[pOut[[-1]]] > 0),
                            {#1 + {- #3[[2]] / 2, 0}, #1 + {#3[[2]] / 2, 0}}, {#1 + {0, - #3[[2]] / 2}, #1 + {0, #3[[2]] / 2}}], "",
                             "ArrowSize" -> dir, "ArrowPosition" -> arrowPos,
                             "Multiply" -> multiply, "MultiplyWidthIn" -> productWidth, "MultiplyWidthOut" -> productWidth,
                             "Style" -> style]
                    }
                ],

                procTagQ[q, "empty" | "sum"],
                {} &,

                procTagQ[q, "initial" | "terminal"],
                With[{xs = Range @ Length @ pIn
                },
                    Table[
                    With[{
                        multiply = With[{arity = typeArity[pIn[[i]]]}, If[TrueQ[OptionValue["ThickDoubleWire"]] && arity == 2, 1, arity]],
                        style = If[TrueQ[OptionValue["ThickDoubleWire"]] && typeArity[pIn[[i]]] == 2, Thickness[Large], Thickness[Medium]]},
                    {
                        Black,
                        Wire[#1 + {edgeSideShift[i, #3, pInArity], - #3[[2]] / 2}, #1 + {edgeSideShift[i, #3, pOutArity], #3[[2]] / 2}, "",
                             "ArrowSize" -> 0,
                             "Multiply" -> multiply, "MultiplyWidthIn" -> productWidth, "MultiplyWidthOut" -> productWidth,
                             "Style" -> style]
                    }
                    ], {i, xs}] &
                ],

                procTagQ[p, "permutation"],
                With[{xs = Range @ Length @ qIn,
                      empties = First /@ Position[qIn, t_ /; typeArity[t] == 0],
                      in = If[procTagQ[p, "circuit"], procInput[q], qIn],
                      inArity = If[procTagQ[q, "circuit"], procInArity[q], qInArity],
                      outArity = If[procTagQ[q, "circuit"], procOutArity[q], qOutArity],
                      perm = InversePermutation @ If[procTagQ[q, "double"], procData[procData[q]["Double"]], procData[q]]["Permutation"]},
                    Function[{coord, v, size},
                        MapThread[Function[{fromIndex, toIndex}, With[{
                            fromShift = {edgeSideShift[fromIndex, size, inArity], - size[[2]] / 2} ,
                            toShift = {edgeSideShift[toIndex, size, outArity], size[[2]] / 2},
                            dir = (1 - 2 Boole @ dualTypesQ[in[[fromIndex]]]) Boole[TrueQ[OptionValue["ShowProcessArrows"]]],
                            multiply = With[{arity = typeArity[in[[fromIndex]]]}, If[TrueQ[OptionValue["ThickDoubleWire"]] && arity == 2, 1, arity]],
                            style = If[TrueQ[OptionValue["ThickDoubleWire"]] && typeArity[in[[fromIndex]]] == 2, Thickness[Large], Thickness[Medium]]
                        },
                        {
                            Black,
                            Wire[coord + fromShift, coord + toShift, "",
                                 "ArrowSize" -> dir, "ArrowPosition" -> arrowPos / 2,
                                 "Multiply" -> multiply, "MultiplyWidthIn" -> productWidth, "MultiplyWidthOut" -> productWidth,
                                 "Style" -> style]
                        }
                        ]
                        ], If[procTagQ[q, "circuit"], reorder @@ DeleteCases[#, Alternatives @@ empties, All] &, Identity] @ {xs, Permute[xs, perm]}]
                    ]
                ],

                procTagQ[q, "cup"],
                With[{arity = typeArity[Join[out, in][[1]]]},
                With[{multiplicity = If[TrueQ[OptionValue["ThickDoubleWire"]] && arity == 2, 1, arity],
                      style = If[TrueQ[OptionValue["ThickDoubleWire"]] && arity == 2, Thickness[Large], Thickness[Medium]],
                      dir = Sign @ Fold[Subtract, 1 - 2 Boole[dualTypesQ /@ Join[out, in]]] Boole[TrueQ[OptionValue["ShowProcessArrows"]]]},
                Function[{coord, v, size}, {
                    Black,
                    Wire[coord + {edgeSideShift[2, size, 2], size[[2]] / 2},
                         coord + {edgeSideShift[1, size, 2], size[[2]] / 2}, "",
                         "VerticalShift" -> 1 / 2, "ArrowSize" -> dir, "Direction" -> "DownArc",
                         "Multiply" -> multiplicity, "MultiplyWidthIn" -> productWidth, "MultiplyWidthOut" -> productWidth,
                         "Reverse" -> True, "Style" -> style]
                }]
                ]],

                procTagQ[q, "curry"],
                With[{arities = typeArity /@ qIn},
                With[{n = Length @ qIn,
                      multiplicity = If[TrueQ[OptionValue["ThickDoubleWire"]] && # == 2, 1, #] & /@ arities,
                      style = If[TrueQ[OptionValue["ThickDoubleWire"]] && # == 2, Thickness[Large], Thickness[Medium]] & /@ arities,
                      dir = (1 - 2 Boole @ dualTypesQ[qOut[[1]]]) Boole[TrueQ[OptionValue["ShowProcessArrows"]]]},
                With[{table = Table[
                        Inactivate[Wire[#1 + {edgeSideShift[i, #3, n], - #3[[2]] / 2},
                             #1 + {edgeSideShift[i, {1, 1}, n] productWidth, #3[[2]] / 2}, "",
                             "ArrowSize" -> dir[[i]], "ArrowPosition" -> arrowPos,
                             "Multiply" -> multiplicity[[i]], "MultiplyWidthIn" -> productWidth, "MultiplyWidthOut" -> productWidth,
                             "Style" -> style[[i]]
                        ], Part | Plus | Times],
                        {i, n}
                    ]
                },
                Activate @ Function[{
                    Black,
                    table
                }]
                ]]]
                ,

                procTagQ[q, "discard"],
                Function[{coord, v, size}, {
                    Black,
                    Wire[coord + {0, - size[[2]] / 2},
                         coord, "", "ArrowSize" -> 0],
                    Thick,
                    Line[{coord + {- size[[1]] / 2, 0}, coord + {size[[1]] / 2, 0}}],
                    Line[{coord + {- size[[1]] / 4, size[[2]] / 4}, coord + {size[[1]] / 4, size[[2]] / 4}}],
                    Line[{coord + {- size[[1]] / 8, size[[2]] / 2}, coord + {size[[1]] / 8, size[[2]] / 2}}]
                }]
                ,

                True,
                outlineShapeFun
            ]
        ];
        If[ procTagQ[p, "double"],
            With[{fun = shapeFun},
                shapeFun = {EdgeForm[{Black, Opacity[1], Thick}], fun[##]} &
            ]
        ];
        With[{fun = shapeFun, outlineFun = outlineShapeFun, scale = If[procTagQ[p, "composite"], {1.25, 1.25}, {1, 1}]},
            If[ TrueQ[OptionValue["Outline"]] && ! procTagQ[q, "initial" | "terminal"],
                shapeFun = Function[{
                    fun[##],
                    FaceForm[Transparent], EdgeForm[Dashed],
                    GeometricTransformation[outlineFun[##], ScalingTransform[scale, #1]]
                }]
            ]
        ];
        With[{fun = shapeFun, transform = {
                If[procTagQ[p, "transpose"], RotationTransform[Pi, #], Nothing],
                If[procTagQ[p, "adjoint"], ReflectionTransform[{0, 1}, #], Nothing]
            }},
            If[ Length[transform] > 0,
                shapeFun = Fold[GeometricTransformation, fun[##], transform] &
            ]
        ];
        With[{
            fun = shapeFun,
            faceForm = If[! MissingQ[procData[p]["Basis"]], FaceForm[Gray], FaceForm[Transparent]],
            inLabels = Table[If[typeArity[If[procTagQ[p, "circuit"], pIn, in][[i]]] > 0, Inactivate[
                With[{pos = posScale[#1, {
                    If[ procTagQ[q, "circuit"],
                        If[ i == 1, - #3[[1]] / 2,
                            edgeSideShift[i - 1, #3, pInArity - 1]
                        ],
                        edgeSideShift[i, #3, inArity]
                    ],
                    If[procTagQ[p, "circuit"] && i == 1, 0, - #3[[2]] / 2]
                    }
                    ]},
                    {
                        Point[pos],
                        If[ TrueQ @ OptionValue["ShowWireLabels"],
                            Text[Style[If[procTagQ[p, "circuit"], pIn, in][[i]], Bold, Black, FontSize -> Small], pos + {1, - 1} / 8],
                            Nothing
                        ]
                    }
                ], Plus | Part | Times], {}],
                {i, Range[If[procTagQ[p, "circuit"], pInArity, inArity]]}
            ],
            outLabels = Table[If[typeArity[If[procTagQ[p, "circuit"], pOut, out][[i]]] > 0, Inactivate[
                With[{pos = posScale[#1, {
                    If[ procTagQ[p, "circuit"],
                        If[ i == pOutArity, #3[[1]] / 2,
                            edgeSideShift[i, #3, pOutArity - 1]
                        ],
                        edgeSideShift[i, #3, outArity]],
                        If[procTagQ[p, "circuit"] && i == pOutArity, 0, #3[[2]] / 2]
                        }
                    ]},
                    {
                        Point[pos],
                        If[ TrueQ[OptionValue["ShowWireLabels"]],
                            Text[Style[If[procTagQ[p, "circuit"], pOut, out][[i]], Bold, Black, FontSize -> Small], pos + {1, 1} / 8],
                            Nothing
                        ]
                    }
                ], Plus | Part | Times], {}],
                {i, Range[If[procTagQ[p, "circuit"], pOutArity, outArity]]}
            ]
        },
            With[{shapeFunBody = {
                    faceForm, Inactive[fun][##],
                    If[! topologicalProcQ[p], {Black, PointSize[Medium], inLabels, outLabels} , Nothing]
                }
            },
                shapeFun = Function[shapeFunBody] // Activate
            ]
        ]];
        shapeFun
        ]
      }
    ]},
    (* edges *)
    {}
    ]
]


ProcGraph[Proc[f : _Composition | _CircleTimes | _Plus, args__], opts : OptionsPattern[]] :=
    ProcGraph[Proc[Defer[f], args], opts]


ProcGraph[Proc[Labeled[Defer[Plus[ps__Proc]], _] | Defer[Plus[ps__Proc]], ___], opts : OptionsPattern[]] := Inactive[Plus] @@ (ProcGraph[#, opts] & /@ {ps})


ProcGraph[p : Proc[Labeled[Defer[CircleTimes[ps__Proc]], _] | Defer[CircleTimes[ps__Proc]], in_, out_, ___], opts : OptionsPattern[]] := Module[{
    graphs, size,
    graphWidths, graphHeights,
    wideProcPositions, qs,
    parallelComposeDistance,
    vertices, edges,
    vertexSize, vertexCoordinates,
    vertexXShifts, vertexYShifts, vertexCoordinateShifts,
    shiftedGraphs,
    newVertexSize, newVertexCoordinates
},
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
            {{ps}, graphWidths, procArity /@ {ps}, graphs}
        ];
        {graphWidths, graphHeights} = Transpose[graphSize /@ graphs];
    ];
    parallelComposeDistance = Replace[OptionValue["ParallelComposeDistance"], Automatic -> If[size[[1]] =!= Automatic,
        Max[(size[[1]] - Total[graphWidths]) / (Length[{ps}] - 1), 0],
        1
    ]];
    vertices = VertexList /@ graphs;
    edges = Catenate[EdgeList /@ graphs];
    edges = Join[
        edges,
        Catenate @ Map[Function[q, With[{var = Last @ procLabel[q]}, Map[
            If[! FreeQ[#, var], Annotation[UndirectedEdge[q, #], EdgeStyle -> Dotted], Nothing] &,
            Select[Catenate[vertices], # =!= q &]
        ]]],
            Select[Catenate[vertices], procTagQ[#, "sum"] &]
        ]
    ];
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
    newVertexSize = Association @ vertexSize;
    Scan[
        Apply @ Function @ With[{
            bottomLeftCorner = First @ SortBy[VertexList[#1], newVertexCoordinates],
            bottomRightCorner = Last @ SortBy[VertexList[#1], newVertexCoordinates[#] {1, -1} &],
            topLeftCorner = First @ SortBy[VertexList[#2], newVertexCoordinates[#] {1, -1} &],
            procs = VertexList[#2]},
        With[{shift = newVertexCoordinates[bottomRightCorner] - newVertexCoordinates[topLeftCorner]},
        Scan[Function[{proc},
            If[ procTagQ[proc, "circuit"] && procTagQ[bottomRightCorner, "circuit"] && procTagQ[topLeftCorner, "circuit"],
                newVertexCoordinates[proc] = newVertexCoordinates[proc] + shift + OptionValue["CircuitDistance"] {1, - 1};
            ]
        ],
            procs
        ]]],
        Partition[shiftedGraphs, 2, 1]
    ];
    Graph[Catenate @ vertices, edges,
        VertexCoordinates -> Normal @ newVertexCoordinates,
        VertexSize -> Normal @ newVertexSize,
        VertexLabels -> Catenate[AnnotationValue[#, VertexLabels] & /@ graphs],
        VertexShapeFunction -> Catenate[AnnotationValue[#, VertexShapeFunction] & /@ graphs],
        EdgeShapeFunction -> Catenate[Replace[AnnotationValue[#, EdgeShapeFunction], Automatic -> {}] & /@ graphs]
    ]
]

ProcGraph[p : Proc[Labeled[Defer[Composition[ps__Proc]], _] | Defer[Composition[ps__Proc]], ___], opts : OptionsPattern[]] := Module[{
    graphs, size,
    composeDistance,
    vertices, edges,
    graphWidths, graphHeights,
    vertexSize, vertexCoordinates,
    inBetweenEdges, allEdges,
    vertexXShifts, vertexYShifts, vertexCoordinateShifts,
    shiftedGraphs,
    newVertexCoordinates, newVertexSize
},
    size = Replace[OptionValue["Size"], Automatic -> {Automatic, Automatic}];
    graphs = Map[ProcGraph[#, "AddTerminals" -> False, "Size" -> {size[[1]], Automatic}, opts] &, {ps}];
    {graphWidths, graphHeights} = Transpose[graphSize /@ graphs];
    If[ size[[1]] === Automatic,
        graphs = Map[ProcGraph[#, "AddTerminals" -> False, "ParallelComposeDistance" -> Automatic,
        "Size" -> {Max[graphWidths], size[[2]]}, opts] &, {ps}];
        {graphWidths, graphHeights} = Transpose[graphSize /@ graphs];
    ];
    graphs = MapThread[shiftVertices[#1, #2] &, {graphs, Minus @* graphCenter /@ graphs}];
    composeDistance = If[size[[2]] === Automatic,
        Replace[OptionValue["ComposeDistance"], Automatic -> 1],
        Max[(size[[2]] - Total[graphHeights]) / (Length[{ps}] - 1), 0]
    ];
    vertices = VertexList /@ graphs;
    edges = Catenate[EdgeList /@ graphs];
    vertexSize = AnnotationValue[#, VertexSize] & /@ graphs;
    vertexCoordinates = GraphEmbedding /@ graphs;
    vertexXShifts = Map[- Mean[#] &, vertexCoordinates[[All, All, 1]]];
    vertexYShifts = FoldList[
        #1 - #2 - composeDistance &,
        0,
        Map[Mean, Partition[graphHeights, 2, 1]]
    ];
    vertexCoordinateShifts = Thread[{vertexXShifts, vertexYShifts}];
    inBetweenEdges = Apply[betweenEdges] /@ Partition[{ps}, 2, 1];
    allEdges = Join[edges, Catenate @ inBetweenEdges];
    shiftedGraphs = MapThread[shiftVertices, {graphs, vertexCoordinateShifts}];
    shiftedGraphs = MapThread[shiftVertices[#1, {#2[[1]], 0}] &, {shiftedGraphs, Minus @* graphCenter /@ shiftedGraphs}];
    newVertexCoordinates = Association[graphVertexCoordinates /@ shiftedGraphs];
    newVertexSize = Association @ vertexSize;
    Scan[
        Apply @ Function @ With[{
            bottomLeftCorner = First @ SortBy[VertexList[#1], newVertexCoordinates],
            bottomRightCorner = First @ SortBy[VertexList[#1], Reverse[newVertexCoordinates[#]] &],
            topLeftCorner = First @ SortBy[VertexList[#2], newVertexCoordinates[#] {1, -1} &],
            procs = VertexList[#2]},
        With[{shift = newVertexCoordinates[topLeftCorner] - newVertexCoordinates[bottomLeftCorner],
              distance = Min[DeleteCases[Differences[Sort[newVertexCoordinates[#][[2]] & /@ VertexList[#1]]], 0]] /. Infinity -> OptionValue["CircuitDistance"]
             },
        Scan[Function[{proc},
            If[ procTagQ[bottomLeftCorner, "circuit"] || procTagQ[topLeftCorner, "circuit"],
                If[ procTagQ[proc, "circuit"],
                    newVertexCoordinates[proc] = newVertexCoordinates[proc] - shift + {0, - distance},
                    (*Echo[{proc, topLeftCorner, bottomRightCorner, newVertexCoordinates, SortBy[VertexList[#1], newVertexCoordinates[#][[2]]]}];*)
                    newVertexCoordinates[proc] = newVertexCoordinates[proc] -
                     {0, (newVertexCoordinates[topLeftCorner] - newVertexCoordinates[bottomRightCorner])[[2]] + distance}
                ]
            ]
        ],
            procs
        ]]],
        Partition[shiftedGraphs, 2, 1]
    ];
    Scan[With[{
        shift = graphCenter[newVertexCoordinates[[Key /@ VertexList[#]]],
            Association[# -> If[procTagQ[#, "circuit"], {1, 1}, newVertexSize[#]] & /@ VertexList[#]]]
    },
        newVertexCoordinates[#] -= {shift[[1]], 0} & /@ VertexList[#]] &,
        shiftedGraphs
    ];
    withProcGraphEdgeShapeFunction[
        Graph[Catenate @ vertices, allEdges,
            VertexCoordinates -> Normal @ newVertexCoordinates,
            VertexSize -> Normal @ newVertexSize,
            VertexLabels -> Catenate[AnnotationValue[#, VertexLabels] & /@ graphs],
            VertexShapeFunction -> Catenate @ Map[AnnotationValue[#, VertexShapeFunction] &, graphs],
            EdgeStyle -> Catenate @ Map[AnnotationValue[#, EdgeStyle] /. Automatic -> Nothing &, graphs]
        ],
        opts
    ]
]


withProcGraphEdgeShapeFunction[g_Graph, opts : OptionsPattern[ProcGraph]] := With[{
    productWidth = Replace[OptionValue[ProcGraph, {opts}, "ProductWidth"], Automatic -> 1 / 10],
    arrowPosition = OptionValue[ProcGraph, {opts}, "ArrowPosition"],
    showLabels = OptionValue[ProcGraph, {opts}, "ShowArrowLabels"],
    thickDoubleWire = OptionValue[ProcGraph, {opts}, "ThickDoubleWire"],
    vertexCoordinate = graphVertexCoordinates[g],
    vertexSize = Association @ AnnotationValue[g, VertexSize]
},
    Annotate[g, EdgeShapeFunction -> Map[Function[e,
        With[{i = e[[3, 1]], j = e[[3, 2]], v = e[[1]], w = e[[2]],
            vIn = procInput[e[[1]], True], vOut = procOutput[e[[1]], True],
            wIn = procInput[e[[2]], True], wOut = procOutput[e[[2]], True],
            vInArity = procInArity[e[[1]], True], vOutArity = procOutArity[e[[1]], True],
            wInArity = procInArity[e[[2]], True], wOutArity = procOutArity[e[[2]], True]
        },
            With[{
                fromShiftIn = edgeSideShift[i + Boole[procTagQ[v, "circuit"]], vertexSize[v], vInArity],
                toShiftOut = edgeSideShift[j - Boole[procTagQ[w, "circuit"]], vertexSize[w], wOutArity],
                multiplicity = If[TrueQ[thickDoubleWire] && typeArity[vOut[[i]]] == 2, 1, typeArity[vOut[[i]]]],
                multiplyWidthIn = productWidth,
                multiplyWidthOut = productWidth,
                vsize = vertexSize[v], wsize = vertexSize[w],
                inType =If[e[[3, 0]] === DownArrow, vIn[[i]], vOut[[i]]],
                outType = If[e[[3, 0]] === UpArrow, wOut[[j]], wIn[[j]]],
                label = If[TrueQ[showLabels] && Not[procTagQ[v, "id"]], If[e[[3, 0]] === DownArrow, vIn[[i]], vOut[[i]]], ""],
                style = If[TrueQ[thickDoubleWire] && typeArity[If[e[[3, 0]] === DownArrow, vIn[[i]], vOut[[i]]]] == 2, Thickness[Large], Thickness[Medium]]
            },
            With[{
                dir = With[{sign = 1 - 2 Boole @ dualTypesQ[inType]}, If[dualType[inType] === outType || Total[sign] == 0, 0, sign]],
                fromShift = If[procTagQ[v, "circuit"], If[i == vOutArity, vsize[[1]] / 2, edgeSideShift[i, vsize, vOutArity - 1]], edgeSideShift[i, vsize, vOutArity]],
                toShift = If[procTagQ[w, "circuit"], If[j == 1, - wsize[[1]] / 2, edgeSideShift[j - 1, wsize, wInArity - 1]], edgeSideShift[j, wsize, wInArity]],
                fromShiftY = If[procTagQ[v, "circuit"] && i == vOutArity, 0, vsize[[2]] / 2],
                toShiftY = If[procTagQ[w, "circuit"] && j == 1, 0, wsize[[2]] / 2],
                fromShiftScale = If[procTagQ[v, "spider"], #1 + Normalize[#2] vsize / 2 &, Plus],
                toShiftScale = If[procTagQ[w, "spider"], #1 + Normalize[#2] wsize / 2 &, Plus]
            },
                With[{fun = Which[
                    e[[3, 0]] === DownArrow,
                    Wire[fromShiftScale[#1[[1]], {fromShiftIn, - fromShiftY}], toShiftScale[#1[[-1]], {toShift, - toShiftY}],
                        label,
                        "ArrowSize" -> (- dir), "ArrowPosition" -> arrowPosition, "Direction" -> "DownArc",
                        "Multiply" -> multiplicity, "MultiplyWidthIn" -> multiplyWidthIn, "MultiplyWidthOut" -> multiplyWidthOut,
                        "Style" -> style] &,
                    e[[3, 0]] === UpArrow,
                    Wire[fromShiftScale[#1[[1]], {fromShift, fromShiftY}], toShiftScale[#1[[-1]], {toShiftOut, toShiftY}],
                        label,
                        "ArrowSize" -> dir, "ArrowPosition" -> arrowPosition, "Direction" -> "UpArc",
                        "Multiply" -> multiplicity, "MultiplyWidthIn" -> multiplyWidthIn, "MultiplyWidthOut" -> multiplyWidthOut,
                        "Style" -> style] &,
                    vertexCoordinate[v][[2]] > vertexCoordinate[w][[2]] && ! procTagQ[v, "circuit"] && ! procTagQ[w, "circuit"],
                    Wire[fromShiftScale[#1[[1]], {fromShift, fromShiftY}], toShiftScale[#1[[-1]], {toShift, - toShiftY}],
                        label,
                        "ArrowSize" -> dir, "ArrowPosition" -> arrowPosition,
                        "HorizontalShift" -> (fromShift + toShift) / 2 - vertexCoordinate[v][[1]],
                        "Multiply" -> multiplicity, "MultiplyWidthIn" -> multiplyWidthIn, "MultiplyWidthOut" -> multiplyWidthOut,
                        "Direction" -> "Loop", "Style" -> style
                    ] &,
                    True,
                    Wire[fromShiftScale[#1[[1]], {fromShift, fromShiftY}], toShiftScale[#1[[-1]], {toShift, - toShiftY}],
                        label,
                        "ArrowSize" -> dir, "ArrowPosition" -> arrowPosition,
                        "Multiply" -> multiplicity, "MultiplyWidthIn" -> multiplyWidthIn, "MultiplyWidthOut" -> multiplyWidthOut,
                        "Style" -> style,
                        "Append" -> If[procTagQ[w, {"spider", "topological"}], #1[[-1]], None],
                        "Prepend" -> If[procTagQ[v, {"spider", "topological"}], #1[[1]], None]] &
                ]},
                    e -> Function[{Black, fun[##]}]
                ]
            ]
            ]
        ]],
        EdgeList[g, _DirectedEdge]
    ]]
]


simplifyProcGraph[g_Graph, opts : OptionsPattern[ProcGraph]] := withProcGraphEdgeShapeFunction[
    Composition[
        simplifyCaps, simplifyCups,
        FixedPoint[simplifyPermutations, #] &,
        simplifyIdentities, If[TrueQ[OptionValue[ProcGraph, {opts}, "AddTerminals"]], Identity, simplifyTerminals],
        simplifyVoids][g],
    opts
]


simplifyIdentities[g_Graph] := Module[{
    procs, ins, outs
},
    procs = Select[VertexList[g], procTagQ["id"]];
    ins = With[{v = SelectFirst[VertexInComponent[g, #], Not @* procTagQ["id"]]},
            If[MissingQ[v], Missing[], First @ EdgeList[g, DirectedEdge[Sequence @@ FindPath[g, v, #][[1, ;; 2]], ___]]]] & /@ procs;
    outs = With[{v = SelectFirst[VertexOutComponent[g, #], Not @* procTagQ["id"]]},
            If[MissingQ[v], Missing[], First @ EdgeList[g, DirectedEdge[Sequence @@ FindPath[g, #, v][[1, - 2 ;;]], ___]]]] & /@ procs;
    EdgeAdd[
        VertexDelete[g, procs],
        DeleteDuplicates @ MapThread[If[MissingQ[#1] || MissingQ[#2],
                Nothing,
                DirectedEdge[#1[[1]], #2[[2]], #1[[3, 1]] -> #2[[3, 2]]]
            ] &,
            {ins, outs}
        ]
    ]
]


simplifyPermutations[g_Graph] := Module[{
    proc, arity, in, out
},
    proc = SelectFirst[VertexList[g], procTagQ["permutation"]];
    If[MissingQ[proc], Return[g]];
    arity = procInArity[proc];
    in = First[EdgeList[g, DirectedEdge[_, proc, _[_, #]]], Missing[]] & /@ Range[arity];
    out = First[EdgeList[g, DirectedEdge[proc, _, _[#, _]]], Missing[]] & /@ Range[arity];
    EdgeAdd[
        VertexDelete[g, proc],
        MapThread[
            If[ MissingQ[#1] || MissingQ[#2],
                Nothing,
                DirectedEdge[#1[[1]], #2[[2]], #1[[3, 1]] -> #2[[3, 2]]]
            ] &,
            {Permute[in, If[procTagQ[proc, "double"], procData[procData[proc]["Double"]], procData[proc]]["Permutation"]], out}
        ]
    ]
]


simplifyVoids[g_Graph] := VertexDelete[g, Select[VertexList[g], procTagQ["empty"]]]


simplifyTerminals[g_Graph] := VertexDelete[g, Select[VertexList[g], procTagQ["initial" | "terminal"]]]


simplifyCups[g_Graph] := Module[{
    procs, outs
},
    procs = Select[VertexList[g], procTagQ[#, "cup"] && ! procRotatedQ[#] &];
    outs = SortBy[EdgeList[g, DirectedEdge[#, __] | DirectedEdge[_, #, ___]], #[[3, 1]] &] & /@ procs;
    EdgeAdd[
        VertexDelete[g, procs],
        MapThread[Function[{out, p},
            With[{a = If[out[[1, 3, 0]] === Rule && Length[out] == 2, 2, 1], b = If[out[[1, 3, 0]] =!= Rule && Length[out] == 2, 2, 1]},
            With[{id1 = If[out[[a, 1]] === p, 2, 1], id2 = If[out[[b, 1]] === p, 2, 1], arrow1 = out[[a, 3, 0]], arrow2 = out[[b, 3, 0]]},
            Which[
                Length[out] == 2,
                DirectedEdge[out[[a, id1]], out[[b, id2]], Which[arrow1 === arrow2 === UpArrow, UpArrow, arrow1 === arrow2 === Rule, DownArrow, True, Rule][out[[a, 3, id1]], out[[b, 3, id2]]]],
                Length[out] == 1 && out[[1, 1]] =!= out[[1, 2]],
                DirectedEdge[out[[1, id1]], out[[1, id1]], id1 -> out[[1, 3, id1]]],
                True,
                Nothing
            ]]]],
            {outs, procs}
        ]
    ]
]


simplifyCaps[g_Graph] := Module[{
    procs, ins
},
    procs = Select[VertexList[g], procTagQ[#, "cup"] && procRotatedQ[#] &];
    ins = SortBy[EdgeList[g, DirectedEdge[_, #, ___] | DirectedEdge[#, ___]], #[[3, 2]] &] & /@ procs;
    EdgeAdd[
        VertexDelete[g, procs],
        MapThread[Function[{in, p},
            With[{a = If[in[[1, 3, 0]] =!= Rule && Length[in] == 2, 2, 1], b = If[in[[1, 3, 0]] === Rule && Length[in] == 2, 2, 1]},
            With[{id1 = If[in[[a, 1]] === p, 2, 1], id2 = If[in[[b, 1]] === p, 2, 1], arrow1 = in[[a, 3, 0]], arrow2 = in[[b, 3, 0]]},
            Which[
                Length[in] == 2,
                DirectedEdge[in[[a, id1]], in[[b, id2]], Which[arrow1 === arrow2 === DownArrow, DownArrow, arrow1 === arrow2 === Rule, UpArrow, True, Rule][in[[a, 3, id1]], in[[b, 3, id2]]]],
                Length[in] == 1 && in[[1, id1]] =!= in[[1, id2]],
                DirectedEdge[in[[1, id1]], in[[1, id1]], in[[1, 3, id1]] -> in[[1, 3, id1]]],
                True,
                Nothing
            ]]]],
            {ins, procs}
        ]
    ]
]
