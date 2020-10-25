Package["DiagramProcess`"]

PackageExport["ProcGraph"]
PackageExport["simplifyProcGraph"]


Options[ProcGraph] = {
    "ComposeDistance" -> Automatic,
    "ParallelComposeDistance" -> Automatic,
    "AddTerminals" -> False,
    "OutlineProcess" -> False,
    "ShowArrowLabels" -> False,
    "ShowProcessLabels" -> True,
    "ShowWireLabels" -> True,
    "ArrowPosition" -> Automatic,
    "Size" -> Automatic};


ProcGraph[p : Proc[Except[_Defer], in_, out_, ___], opts : OptionsPattern[]] := Module[{vertexSize, vertexCoords, graph = None, shapeFun, outlineShapeFun},
    If[TrueQ[OptionValue["AddTerminals"]],
        Return @ ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];
    vertexCoords = {0, 0};
    vertexSize = MapAt[Min[Replace[#, Automatic -> 1], 1] & ,
        MapAt[Replace[Automatic -> Max[procArity[p], 1]], Replace[OptionValue["Size"], Automatic -> {Automatic, Automatic}], 1],
        2
    ];
    If[ MatchQ[procTag[p], "initial" | "terminal"],
        vertexCoords = vertexCoords + If[procTag[p] == "initial", {0, vertexSize[[2]] / 2}, {0, - vertexSize[[2]] / 2}];
        vertexSize = vertexSize {1, 0}
    ];
    If[ MatchQ[procLabel[p], "Composite"[_]],
        graph = ProcGraph[ReplacePart[p, 1 -> procFunc[p]], "AddTerminals" -> True, "OutlineProcess" -> False];
        vertexSize = graphSize[graph];
        vertexCoords = graphCenter[graph]
    ];
    Graph[{Annotation[p, {
        VertexCoordinates -> vertexCoords,
        VertexSize -> vertexSize,
        VertexShapeFunction -> With[{
                inArity = Length[in], outArity = Length[out],
                label = procLabel[p],
                tag = procTag[p],
                arrowPos = OptionValue["ArrowPosition"] /. Automatic -> 0.5,
                shape = With[{q = Which[
                    MatchQ[procLabel[p], "Transpose"[_]],
                    transposeProc[p],
                    MatchQ[procLabel[p], _SuperDagger],
                    adjointProc[p],
                    MatchQ[procLabel[p], _OverBar],
                    conjugateProc[p],
                    True,
                    p
                ]},
                    Which[
                        MatchQ[procLabel[p], "Composite"[_]],
                        "Rectangle",
                        procArity[q] == 0,
                        "Diamond",
                        procInArity[q] == 0,
                        "DownTriangle",
                        procOutArity[q] == 0,
                        "UpTriangle",
                        True,
                        "Trapezoid"
                    ]
                ]
        },
            outlineShapeFun = procShape[#1, #3[[1]], #3[[2]], "Shape" -> shape] &;

            With[{fun = outlineShapeFun},
                outlineShapeFun = Which[
                    MatchQ[label, "Transpose"[_]],
                    GeometricTransformation[fun[##], RotationTransform[Pi, #1]] &,
                    MatchQ[label, _SuperDagger],
                    GeometricTransformation[fun[##], ReflectionTransform[{0, 1}, #1]] &,
                    MatchQ[label, _OverBar],
                    GeometricTransformation[fun[##], ReflectionTransform[{1, 0}, #1]] &,
                    True,
                    fun
                ]
            ];

            shapeFun = If[MatchQ[label, "Composite"[_]],
                With[{graphics = First[GraphPlot[graph]], center = graphCenter[graph]},
                    GeometricTransformation[graphics, TranslationTransform[#1 - center]] &
                ],
                Which[
                MatchQ[tag, "id" | "cast"],
                Function @ With[{dir = 1 - 2 Boole @ dualTypeQ[#2[[2, 1]]]},
                    {
                        Black,
                        ArrowUp[#1 + {0, - 1 / 2}, #1 + {0, 1 / 2}, "",
                                "ArrowSize" -> 0 * dir, "ArrowPosition" -> arrowPos]
                    }
                ],

                MatchQ[tag, "empty" | "sum"],
                {} &,

                MatchQ[tag, "initial" | "terminal"],
                With[{xs = Range @ Length @ in},

                    Function[{coord, v, size},
                        Map[Function[index, With[{
                            fromShift = {edgeSideShift[index, size, inArity], - size[[2]] / 2},
                            toShift = {edgeSideShift[index, size, outArity], size[[2]] / 2}
                        },
                        {
                            Black,
                            ArrowUp[coord + fromShift, coord + toShift, "",
                                    "ArrowSize" -> 0]
                        }
                        ]
                        ], xs]
                    ]
                ],

                MatchQ[tag, "permutation"],
                With[{xs = Range @ Length @ in},

                    Function[{coord, v, size},
                        MapThread[Function[{fromIndex, toIndex}, With[{
                            fromShift = {edgeSideShift[fromIndex, size, inArity], - size[[2]] / 2},
                            toShift = {edgeSideShift[toIndex, size, outArity], size[[2]] / 2},
                            dir = 1 - 2 Boole @ dualTypeQ[v[[2, fromIndex]]]
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
                    (*Arrowheads[{{Medium (2 Boole[dualTypeQ @ out[[1]]] - 1), arrowPos}}],*)
                    Black,
                    BezierCurve @ {
                        coord + {edgeSideShift[1, size, 2], size[[2]] / 2},
                        coord + {edgeSideShift[1, size, 2], 0},
                        coord + {edgeSideShift[2, size, 2], 0},
                        coord + {edgeSideShift[2, size, 2], size[[2]] / 2}
                        }
                }, {
                    (*Arrowheads[{{Medium (1 - 2 Boole[dualTypeQ @ in[[1]]]), arrowPos}}],*)
                    Black,
                    BezierCurve @ {
                        coord + {edgeSideShift[1, size, 2], - size[[2]] / 2},
                        coord + {edgeSideShift[1, size, 2], 0},
                        coord + {edgeSideShift[2, size, 2], 0}, 
                        coord + {edgeSideShift[2, size, 2], - size[[2]] / 2}
                    }
                }]],

                MatchQ[tag, "copy"],
                Function[{coord, v, size}, {
                    Black,
                    Table[
                        ArrowUp[coord + {0, - size[[2]] / 2}, coord + {edgeSideShift[i, size, outArity], size[[2]] / 2}, "",
                                "ArrowPosition" -> arrowPos],
                        {i, Length @ out}
                    ]
                }],

                True,
                outlineShapeFun
            ]];
            With[{fun = shapeFun},
                If[ TrueQ[OptionValue["OutlineProcess"]],
                    shapeFun = Function[{fun[##],
                        FaceForm[Transparent], EdgeForm[Dashed],
                        outlineShapeFun[##]
                    }]
                ]
            ];
            With[{fun = shapeFun,
                inLabels = Inactivate[Table[
                    With[{pos = #1 + {edgeSideShift[i, #3, inArity], - #3[[2]] / 2}},
                        {
                            Point[pos],
                            If[ TrueQ @ OptionValue["ShowWireLabels"],
                                Text[Style[in[[i]], Bold, Black, FontSize -> Small], pos + {1, - 1} / 8],
                                Nothing
                            ]
                        }
                    ],
                        {i, Range[inArity]}
                    ], Plus | Part
                ],
                outLabels = Inactivate[Table[
                    With[{pos = #1 + {edgeSideShift[i, #3, outArity], #3[[2]] / 2}},
                        {
                            Point[pos],
                            If[ TrueQ @ OptionValue["ShowWireLabels"],
                                Text[Style[out[[i]], Bold, Black, FontSize -> Small], pos + {1, 1} / 8],
                                Nothing
                            ]
                        }
                    ],
                        {i, Range[outArity]}],
                    Plus | Part
                ],
                processLabel = If[TrueQ[OptionValue["ShowProcessLabels"]] && ! MatchQ[label, "Composite"[_]], stripProcSupers @ label, ""]
            },
                If[! topologicalProcQ[p],
                    shapeFun = {
                        fun[##],
                        Black, PointSize[Medium],
                        inLabels,
                        outLabels,
                        Text[Style[processLabel, FontSize -> Medium], #1, Center]
                    } & // Activate
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


ProcGraph[Proc[Defer[Plus[ps__Proc]], ___], opts : OptionsPattern[]] := Apply[Plus, ProcGraph[#, opts] & /@ {ps}]


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
    shiftedGraphs = MapThread[shiftVertices, {graphs, vertexCoordinateShifts}];
    shiftedGraphs = MapThread[shiftVertices[#1, {#2[[1]], 0}] &, {shiftedGraphs, Minus @* graphCenter /@ shiftedGraphs}];
    newVertexCoordinates = Association[graphVertexCoordinates /@ shiftedGraphs];
    newVertexSize = Association @ vertexSize;
    withProcGraphEdgeShapeFunction[
        Graph[Catenate @ vertices, allEdges,
            VertexCoordinates -> Normal @ newVertexCoordinates,
            VertexSize -> Normal @ newVertexSize,
            VertexShapeFunction -> Catenate @ Map[AnnotationValue[#, VertexShapeFunction] &, graphs]
        ],
        OptionValue["ArrowPosition"],
        OptionValue["ShowArrowLabels"]
    ]
]


withProcGraphEdgeShapeFunction[g_Graph, arrowPosition_ : 0.5, showLabels_ : True] := With[{
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
                vsize = vertexSize[v], wsize = vertexSize[w],
                dir = Small (1 - 2 Boole @ dualTypeQ[If[e[[3, 0]] === DownArrow, v[[2, i]], v[[3, i]]]]),
                label = If[TrueQ[showLabels] && Not[MatchQ[procTag[v], "id"]], If[e[[3, 0]] === DownArrow, v[[2, i]], v[[3, i]]], ""]
            },
                With[{fun = Which[
                        v === w,
                        ArrowLoop[#1[[1]] + {fromShift, vsize[[2]] / 2}, #1[[-1]] + {toShift, - wsize[[2]] / 2},
                            (fromShift + toShift) / 2 - vertexCoordinate[v][[1]],
                            label,
                            "ArrowSize" -> dir, "ArrowPosition" -> arrowPosition
                        ] &,
                        e[[3, 0]] === DownArrow,
                        ArrowDownLoop[#1[[1]] + {fromShiftIn, - vsize[[2]] / 2}, #1[[-1]] + {toShift, - wsize[[2]] / 2}, label,
                            "ArrowSize" -> Small (2 Boole @ dualTypeQ[v[[2, i]]] - 1), "ArrowPosition" -> arrowPosition] &,
                        e[[3, 0]] === UpArrow,
                        ArrowUpLoop[#1[[1]] + {fromShift, vsize[[2]] / 2}, #1[[-1]] + {toShiftOut, wsize[[2]] / 2}, label,
                            "ArrowSize" -> dir, "ArrowPosition" -> arrowPosition] &,
                        True,
                        ArrowUp[#1[[1]] + {fromShift, vsize[[2]] / 2}, #1[[-1]] + {toShift, - wsize[[2]] / 2} , label,
                            "ArrowSize" -> dir, "ArrowPosition" -> arrowPosition] &
                ]},
                    e -> Function[{Black, fun[##]}]
                ]
            ]
        ]],
        EdgeList[g]
    ]]
]


simplifyProcGraph[g_Graph, OptionsPattern[ProcGraph]] := withProcGraphEdgeShapeFunction[
    simplifyCaps @ simplifyCups @ (FixedPoint[simplifyPermutations, #] &) @ simplifyIdentities @ simplifyVoids @ g, OptionValue["ArrowPosition"], OptionValue["ShowArrowLabels"]
]


simplifyIdentities[g_Graph] := Module[{
    procs, ins, outs
},
    procs = Select[VertexList[g], MatchQ["id"] @* procTag];
    ins = With[{v = SelectFirst[VertexInComponent[g, #], Not @* MatchQ["id"] @* procTag]},
            If[MissingQ[v], Missing[], First @ EdgeList[g, DirectedEdge[Sequence @@ FindPath[g, v, #][[1, ;; 2]], ___]]]] & /@ procs;
    outs = With[{v = SelectFirst[VertexOutComponent[g, #], Not @* MatchQ["id"] @* procTag]},
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
    proc = SelectFirst[VertexList[g], MatchQ["permutation"] @* procTag];
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


simplifyVoids[g_Graph] := VertexDelete[g, Select[VertexList[g], MatchQ["initial" | "terminal" | "empty"] @* procTag]]


simplifyCups[g_Graph] := Module[{
    procs, outs
},
    procs = Select[VertexList[g], MatchQ["cup"] @* procTag];
    outs = SortBy[EdgeList[g, DirectedEdge[#, __]], #[[3, 1]] &] & /@ procs;
    EdgeAdd[
        VertexDelete[g, procs],
        Map[Function[out, Which[
                Length[out] == 2,
                DirectedEdge[out[[1, 2]], out[[2, 2]], DownArrow[out[[1, 3, 2]], out[[2, 3, 2]]]],
                Length[out] == 1,
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
    procs = Select[VertexList[g], MatchQ["cap"] @* procTag];
    ins = SortBy[EdgeList[g, DirectedEdge[_, #, ___]], #[[3, 2]] &] & /@ procs;
    EdgeAdd[
        VertexDelete[g, procs],
        Map[Function[in, Which[
                Length[in] == 2,
                DirectedEdge[in[[1, 1]], in[[2, 1]], UpArrow[in[[1, 3, 1]], in[[2, 3, 1]]]],
                Length[in] == 1,
                DirectedEdge[in[[1, 1]], in[[1, 1]], in[[1, 3, 1]] -> in[[1, 3, 1]]],
                True,
                Nothing
            ]],
            ins
        ]
    ]
]
