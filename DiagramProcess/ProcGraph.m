Package["DiagramProcess`"]

PackageExport["ProcGraph"]
PackageExport["simplifyProcGraph"]


Options[ProcGraph] = {
    "ComposeDistance" -> Automatic,
    "ParallelComposeDistance" -> Automatic,
    "ProductWidth" -> Automatic,
    "AddTerminals" -> False,
    "OutlineProcess" -> False,
    "ShowArrowLabels" -> False,
    "ShowProcessLabels" -> True,
    "ShowWireLabels" -> True,
    "ArrowPosition" -> Automatic,
    "Size" -> Automatic};


ProcGraph[p : Proc[Except[_Defer], in_, out_, ___], opts : OptionsPattern[]] := Module[{
    vertexSize, vertexCoords, vertexLabel, graph = None, shapeFun, outlineShapeFun
},
    If[TrueQ[OptionValue["AddTerminals"]],
        Return @ ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];
    vertexCoords = {0, 0};
    vertexSize = MapAt[Min[Replace[#, Automatic -> 1], 1] & ,
        MapAt[Replace[Automatic -> Max[procArity[p], 1]], Replace[OptionValue["Size"], Automatic -> {Automatic, Automatic}], 1],
        2
    ];
    If[ procTagQ[p, "initial" | "terminal"],
        vertexCoords = vertexCoords + If[procTagQ[p, "initial"], {0, vertexSize[[2]] / 2}, {0, - vertexSize[[2]] / 2}];
        vertexSize = vertexSize {1, 0}
    ];
    If[ procTagQ[p, "composite"],
        graph = ProcGraph[ReplacePart[p, 1 -> procFunc[p]], "AddTerminals" -> True, "OutlineProcess" -> False,
            "ComposeDistance" -> 0, "ParallelComposeDistance" -> 0, opts];
        vertexSize = graphSize[graph];
        vertexCoords = graphCenter[graph]
    ];
    If[ procTagQ[p, "spider"],
        vertexSize = If[ procTagQ[p, "topological"], {1 / 8, 1 / 8}, {1 / 2, 1 / 2}]
    ];
    vertexLabel = If[TrueQ[OptionValue["ShowProcessLabels"]] && ! procTagQ[p, "composite"], stripProcSupers @ procLabel[p], ""];
    Graph[{Annotation[p, {
        VertexCoordinates -> vertexCoords,
        VertexSize -> vertexSize,
        VertexShapeFunction -> With[{
                inArity = Length[in], outArity = Length[out],
                productWidth = OptionValue["ProductWidth"] /. Automatic -> 1 / 10,
                arrowPos = OptionValue["ArrowPosition"] /. Automatic -> 0.5,
                shape = With[{q = Which[
                    procTagQ[p, {"transpose", "adjoint"}],
                    conjugateProc[p],
                    procTagQ[p, "transpose"],
                    transposeProc[p],
                    procTagQ[p, "adjoint"],
                    adjointProc[p],
                    True,
                    p
                ]},
                    Which[
                        procTagQ[p, "zero"],
                        "None",
                        procTagQ[p, "spider"],
                        "Disk",
                        (*procTagQ[p, "composite"],
                        "Rectangle",*)
                        procArity[q] == 0,
                        "Diamond",
                        procInArity[q] == 0,
                        "DownTriangle",
                        procOutArity[q] == 0,
                        "UpTriangle",
                        True,
                        "Trapezoid"
                    ]
                ],
                posScale = With[{size = vertexSize}, If[procTagQ[p, "spider"], #1 + Normalize[#2] size, #1 + #2] &]
        },
            outlineShapeFun = procShape[#1, #3[[1]], #3[[2]], "Shape" -> shape] &;

            With[{fun = outlineShapeFun},
                outlineShapeFun = Which[
                    procTagQ[p, {"transpose", "adjoint"}],
                    GeometricTransformation[fun[##], ReflectionTransform[{1, 0}, #1]] &,
                    procTagQ[p, "transpose"],
                    GeometricTransformation[fun[##], RotationTransform[Pi, #1]] &,
                    procTagQ[p, "adjoint"],
                    GeometricTransformation[fun[##], ReflectionTransform[{0, 1}, #1]] &,
                    True,
                    fun
                ]
            ];

            shapeFun = If[procTagQ[p, "composite"],
                With[{graphics = First[GraphPlot[graph]]},
                    GeometricTransformation[graphics, TranslationTransform[#1 - vertexCoords]] &
                ],
                Which[
                procTagQ[p, "id" | "cast"],
                With[{dir = 1 - 2 Boole @ dualTypeQ[p[[2, 1]]], multiply = typeArity[p[[2, 1]]]},
                    Function @ {
                        Black,
                        Wire[#1 + {0, - 1 / 2}, #1 + {0, 1 / 2}, "",
                             "ArrowSize" -> 0 * dir, "ArrowPosition" -> arrowPos,
                             "Multiply" -> multiply, "MultiplyWidthIn" -> productWidth, "MultiplyWidthOut" -> productWidth]
                    }
                ],

                procTagQ[p, "empty" | "sum"],
                {} &,

                procTagQ[p, "initial" | "terminal"],
                With[{xs = Range @ Length @ in},

                    Function[{coord, v, size},
                        Map[Function[index, With[{
                            fromShift = {edgeSideShift[index, size, inArity], - size[[2]] / 2},
                            toShift = {edgeSideShift[index, size, outArity], size[[2]] / 2}
                        },
                        {
                            Black,
                            Wire[coord + fromShift, coord + toShift, "", "ArrowSize" -> 0]
                        }
                        ]
                        ], xs]
                    ]
                ],

                procTagQ[p, "permutation"],
                With[{xs = Range @ Length @ in},
                    Function[{coord, v, size},
                        MapThread[Function[{fromIndex, toIndex}, With[{
                            fromShift = {edgeSideShift[fromIndex, size, inArity], - size[[2]] / 2},
                            toShift = {edgeSideShift[toIndex, size, outArity], size[[2]] / 2},
                            dir = 1 - 2 Boole @ dualTypeQ[v[[2, fromIndex]]],
                            multiply = typeArity[p[[2, fromIndex]]]
                        },
                        {
                            Black,
                            Wire[coord + fromShift, coord + toShift, "",
                                 "ArrowSize" -> 0 * dir, "ArrowPosition" -> arrowPos / 2,
                                 "Multiply" -> multiply, "MultiplyWidthIn" -> productWidth, "MultiplyWidthOut" -> productWidth]
                        }
                        ]
                        ], {FirstCase[#, _Integer, Missing[], All] & /@ p @@ xs, xs}]
                    ]
                ],

                procTagQ[p, "cup"],
                With[{rotated = procRotatedQ[p], multiply = typeArity[If[procRotatedQ[p], in[[1]], out[[1]]]]},
                Function[{coord, v, size}, If[rotated, {
                    Black,
                    Wire[coord + {edgeSideShift[1, size, 2], - size[[2]] / 2},
                         coord + {edgeSideShift[2, size, 2], - size[[2]] / 2}, "",
                         "VerticalShift" -> 1 / 2, "ArrowSize" -> 0, "Direction" -> "UpArc",
                         "Multiply" -> multiply, "MultiplyWidthIn" -> productWidth, "MultiplyWidthOut" -> productWidth]
                }, {
                    Black,
                    Wire[coord + {edgeSideShift[1, size, 2], size[[2]] / 2},
                         coord + {edgeSideShift[2, size, 2], size[[2]] / 2}, "",
                         "VerticalShift" -> 1 / 2, "ArrowSize" -> 0, "Direction" -> "DownArc",
                         "Multiply" -> multiply, "MultiplyWidthIn" -> productWidth, "MultiplyWidthOut" -> productWidth]
                }
                ]]
                ],

                procTagQ[p, "curry"],
                With[{rotated = procRotatedQ[p]},
                If[rotated,
                Function[{coord, v, size}, {
                    Black,
                    Table[
                        Wire[coord + {edgeSideShift[i, {1, 1}, 2] productWidth, - size[[2]] / 2},
                             coord + {edgeSideShift[i, size, 2], size[[2]] / 2}, "",
                             "ArrowSize" -> 0, "ArrowPosition" -> arrowPos],
                        {i, 2}
                    ]
                }],
                Function[{coord, v, size}, {
                    Black,
                    Table[
                        Wire[coord + {edgeSideShift[i, size, 2], - size[[2]] / 2},
                             coord + {edgeSideShift[i, {1, 1}, 2] productWidth, size[[2]] / 2}, "",
                             "ArrowSize" -> 0, "ArrowPosition" -> arrowPos],
                        {i, 2}
                    ]
                }]
                ]]
                ,

                procTagQ[p, "discard"],
                With[{rotated = procRotatedQ[p]},
                Function[{coord, v, size}, {
                If[rotated, {
                    Black,
                    Wire[coord + {0, size[[2]] / 2},
                         coord, "", "ArrowSize" -> 0]
                    (*Wire[coord + {edgeSideShift[1, {1, 1}, 2] * productWidth, size[[2]] / 2},
                         coord + {edgeSideShift[2, {1, 1}, 2] * productWidth, size[[2]] / 2}, "",
                        "VerticalShift" -> size[[2]] / 2, "ArrowSize" -> 0, "Direction" -> "DownArc"]*)
                }, {
                    Black,
                    Wire[coord + {0, - size[[2]] / 2},
                         coord, "", "ArrowSize" -> 0]
                    (*Wire[coord + {edgeSideShift[1, {1, 1}, 2] * productWidth, - size[[2]] / 2},
                         coord + {edgeSideShift[2, {1, 1}, 2] * productWidth, - size[[2]] / 2}, "",
                        "VerticalShift" -> size[[2]] / 2, "ArrowSize" -> 0, "Direction" -> "UpArc"]*)
                }],
                Black, Thick,
                Line[{coord + {- size[[1]] / 2, 0}, coord + {size[[1]] / 2, 0}}],
                Line[{coord + {- size[[1]] / 4, size[[2]] / 4}, coord + {size[[1]] / 4, size[[2]] / 4}}],
                Line[{coord + {- size[[1]] / 8, size[[2]] / 2}, coord + {size[[1]] / 8, size[[2]] / 2}}]
                }]
                ],

                True,
                outlineShapeFun
            ]];
            If[ procTagQ[p, "double"],
                With[{fun = shapeFun},
                    shapeFun = {EdgeForm[{Black, Opacity[1], Thick}], fun[##]} &
                ]
            ];
            With[{fun = shapeFun, scale = If[procTagQ[p, "composite"], {1.25, 1.25}, {1, 1}]},
                If[ TrueQ[OptionValue["OutlineProcess"]],
                    shapeFun = Function[{
                        fun[##],
                        FaceForm[Transparent], EdgeForm[Dashed],
                        GeometricTransformation[outlineShapeFun[##], ScalingTransform[scale, #1]]
                    }]
                ]
            ];
            With[{
                fun = shapeFun,
                faceForm = If[procTagQ[p, "shaded"], FaceForm[Gray], FaceForm[Transparent]],
                inLabels = Inactivate[Table[
                    With[{pos = posScale[#1, {edgeSideShift[i, #3, inArity], - #3[[2]] / 2}]},
                        {
                            Point[pos],
                            If[ TrueQ @ OptionValue["ShowWireLabels"],
                                Text[Style[in[[i]], Bold, Black, FontSize -> Small], pos + {1, - 1} / 8],
                                Nothing
                            ]
                        }
                    ],
                        {i, Range[inArity]}
                    ], Plus | Part | Times
                ],
                outLabels = Inactivate[Table[
                    With[{pos = posScale[#1, {edgeSideShift[i, #3, outArity], #3[[2]] / 2}]},
                        {
                            Point[pos],
                            If[ TrueQ @ OptionValue["ShowWireLabels"],
                                Text[Style[out[[i]], Bold, Black, FontSize -> Small], pos + {1, 1} / 8],
                                Nothing
                            ]
                        }
                    ],
                        {i, Range[outArity]}],
                    Plus | Part | Times
                ]
            },
                With[{shapeFunBody = {
                        faceForm, Inactive[fun][##],
                        If[! topologicalProcQ[p], {Black, PointSize[Medium], inLabels, outLabels} , Nothing],
                        If[! unlabeledProcQ[p], {Black, Text[Style[vertexLabel, FontSize -> Medium], #1, Center]}, Nothing]
                    }
                },
                    shapeFun = Function[shapeFunBody] // Activate
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


ProcGraph[Proc[f : _Composition | _CircleTimes | _Plus, args__], opts : OptionsPattern[]] :=
    ProcGraph[Proc[Defer[f], args], opts]


ProcGraph[Proc[Defer[Plus[ps__Proc]], ___], opts : OptionsPattern[]] := ProcGraph[#, opts] & /@ {ps}


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
    inBetweenEdges = Catenate[Apply[betweenEdges] /@ Partition[{ps}, 2, 1]];
    allEdges = Join[edges, inBetweenEdges];
    shiftedGraphs = MapThread[shiftVertices, {graphs, vertexCoordinateShifts}];
    shiftedGraphs = MapThread[shiftVertices[#1, {#2[[1]], 0}] &, {shiftedGraphs, Minus @* graphCenter /@ shiftedGraphs}];
    newVertexCoordinates = Association[graphVertexCoordinates /@ shiftedGraphs];
    newVertexSize = Association @ vertexSize;
    withProcGraphEdgeShapeFunction[
        Graph[Catenate @ vertices, allEdges,
            VertexCoordinates -> Normal @ newVertexCoordinates,
            VertexSize -> Normal @ newVertexSize,
            VertexShapeFunction -> Catenate @ Map[AnnotationValue[#, VertexShapeFunction] &, graphs],
            EdgeStyle -> Catenate @ Map[AnnotationValue[#, EdgeStyle] /. Automatic -> Nothing &, graphs]
        ],
        OptionValue["ProductWidth"],
        OptionValue["ArrowPosition"],
        OptionValue["ShowArrowLabels"]
    ]
]


withProcGraphEdgeShapeFunction[g_Graph, productWidth_ : 0.01, arrowPosition_ : 0.5, showLabels_ : True] := With[{
    vertexCoordinate = graphVertexCoordinates[g],
    vertexSize = Association @ AnnotationValue[g, VertexSize]
},
    Annotate[g, EdgeShapeFunction -> Map[Function[e,
        With[{i = e[[3, 1]], j = e[[3, 2]], v = e[[1]], w = e[[2]]},
            With[{
                fromShift = edgeSideShift[i, vertexSize[v], procOutArity[v]],
                toShift = edgeSideShift[j, vertexSize[w], procInArity[w]],
                fromShiftIn = edgeSideShift[i, vertexSize[v], procInArity[v]],
                toShiftOut = edgeSideShift[j, vertexSize[w], procOutArity[w]],
                multiplicity = typeArity[v[[3, i]]],
                multiplyWidthIn = Replace[productWidth, Automatic -> 1 / 10],
                multiplyWidthOut = Replace[productWidth, Automatic -> 1 / 10],
                vsize = vertexSize[v], wsize = vertexSize[w],
                inType =If[e[[3, 0]] === DownArrow, v[[2, i]], v[[3, i]]],
                outType = If[e[[3, 0]] === UpArrow, w[[3, j]], w[[2, j]]],
                label = If[TrueQ[showLabels] && Not[procTagQ[v, "id"]], If[e[[3, 0]] === DownArrow, v[[2, i]], v[[3, i]]], ""]
            },
            With[{
                dir = If[dualType[inType] === outType, 0, 1 - 2 Boole @ dualTypesQ[inType]],
                fromShiftScale = If[procTagQ[v, "spider"], #1 + Normalize[#2] vsize &, Plus],
                toShiftScale = If[procTagQ[w, "spider"], #1 + Normalize[#2] wsize &, Plus]
            },
                With[{fun = Which[
                    v === w,
                    Wire[fromShiftScale[#1[[1]], {fromShift, vsize[[2]] / 2}], toShiftScale[#1[[-1]], {toShift, - wsize[[2]] / 2}],
                        label,
                        "ArrowSize" -> Small dir, "ArrowPosition" -> arrowPosition,
                        "HorizontalShift" -> (fromShift + toShift) / 2 - vertexCoordinate[v][[1]],
                        "Direction" -> "Loop"
                    ] &,
                    e[[3, 0]] === DownArrow,
                    Wire[fromShiftScale[#1[[1]], {fromShiftIn, - vsize[[2]] / 2}], toShiftScale[#1[[-1]], {toShift, - wsize[[2]] / 2}],
                        label,
                        "ArrowSize" -> Small (- dir), "ArrowPosition" -> arrowPosition, "Direction" -> "DownArc"] &,
                    e[[3, 0]] === UpArrow,
                    Wire[fromShiftScale[#1[[1]], {fromShift, vsize[[2]] / 2}], toShiftScale[#1[[-1]], {toShiftOut, wsize[[2]] / 2}],
                        label,
                        "ArrowSize" -> Small dir, "ArrowPosition" -> arrowPosition, "Direction" -> "UpArc"] &,
                    True,
                    Wire[fromShiftScale[#1[[1]], {fromShift, vsize[[2]] / 2}], toShiftScale[#1[[-1]], {toShift, - wsize[[2]] / 2}],
                        label,
                        "ArrowSize" -> Small dir, "ArrowPosition" -> arrowPosition,
                        "Multiply" -> multiplicity, "MultiplyWidthIn" -> multiplyWidthIn, "MultiplyWidthOut" -> multiplyWidthOut] &
                ]},
                    e -> Function[{Black, fun[##]}]
                ]
            ]
            ]
        ]],
        EdgeList[g, _DirectedEdge]
    ]]
]


simplifyProcGraph[g_Graph, OptionsPattern[ProcGraph]] := withProcGraphEdgeShapeFunction[
    simplifyCaps @ simplifyCups @ (FixedPoint[simplifyPermutations, #] &) @ simplifyIdentities @ simplifyVoids @ g,
    OptionValue["ProductWidth"],
    OptionValue["ArrowPosition"],
    OptionValue["ShowArrowLabels"]
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
    arity = Length[proc[[2]]];
    in = First[EdgeList[g, DirectedEdge[_, proc, _[_, #]]], Missing[]] & /@ Range[arity];
    out = First[EdgeList[g, DirectedEdge[proc, _, _[#, _]]], Missing[]] & /@ Range[arity];
    EdgeAdd[
        VertexDelete[g, proc],
        MapThread[
            If[ MissingQ[#1] || MissingQ[#2],
                Nothing,
                DirectedEdge[#1[[1]], #2[[2]], #1[[3, 1]] -> #2[[3, 2]]]
            ] &,
            {proc @@ in, out}
        ]
    ]
]


simplifyVoids[g_Graph] := VertexDelete[g, Select[VertexList[g], procTagQ["initial" | "terminal" | "empty"]]]


simplifyCups[g_Graph] := Module[{
    procs, outs
},
    procs = Select[VertexList[g], procTagQ[#, "cup"] && ! procRotatedQ[#] &];
    outs = SortBy[EdgeList[g, DirectedEdge[#, __]], #[[3, 1]] &] & /@ procs;
    EdgeAdd[
        VertexDelete[g, procs],
        Map[Function[out, Which[
                Length[out] == 2,
                DirectedEdge[out[[1, 2]], out[[2, 2]], DownArrow[out[[1, 3, 2]], out[[2, 3, 2]]]],
                Length[out] == 1 && out[[1, 1]] =!= out[[1, 2]],
                DirectedEdge[out[[1, 2]], out[[1, 2]], out[[1, 3, 2]] -> out[[1, 3, 2]]],
                True,
                Nothing
            ]],
            outs
        ]
    ]
]


simplifyCaps[g_Graph] := Module[{
    procs, ins
},
    procs = Select[VertexList[g], procTagQ[#, "cup"] && procRotatedQ[#] &];
    ins = SortBy[EdgeList[g, DirectedEdge[_, #, ___]], #[[3, 2]] &] & /@ procs;
    EdgeAdd[
        VertexDelete[g, procs],
        Map[Function[in, Which[
                Length[in] == 2,
                DirectedEdge[in[[1, 1]], in[[2, 1]], UpArrow[in[[1, 3, 1]], in[[2, 3, 1]]]],
                Length[in] == 1 && in[[1, 1]] =!= in[[1, 2]],
                DirectedEdge[in[[1, 1]], in[[1, 1]], in[[1, 3, 1]] -> in[[1, 3, 1]]],
                True,
                Nothing
            ]],
            ins
        ]
    ]
]
