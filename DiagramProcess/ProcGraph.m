Package["DiagramProcess`"]

PackageExport["ProcGraph"]


Options[ProcGraph] = {
    "ComposeDistance" -> 1,
    "ParallelComposeDistance" -> 1, "AddTerminals" -> False,
    "OutlineProcess" -> False, "ShowLabels" -> True,
    "ArrowPosition" -> Automatic};

ProcGraph[p : Proc[f_, in_, out_, ___], opts : OptionsPattern[]] := Module[{},
    If[TrueQ[OptionValue["AddTerminals"]],
        Return@ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];

    Graph[{Annotation[p, {
        VertexCoordinates -> {0, 0},
        VertexSize -> {1, 1},
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
                procShape[#1, label, (*outArity/2*)#3[[1]], (*inArity/2*)#3[[1]], #3[[2]]] &
            ]},
            If[TrueQ[OptionValue["OutlineProcess"]],
            {
                shapeFun[##],
                FaceForm[Transparent], EdgeForm[Dashed],
                procShape[#1, "", (*outArity/2*)#3[[1]], (*inArity/2*)#3[[1]], #3[[2]]]
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
    graphs = Map[ProcGraph[#, "AddTerminals" -> False, opts] &, {ps}],
    vertices, edges,
    vertexSize,
    vertexCoordinates,
    vertexXShifts, vertexYShifts,
    vertexCoordinateShifts, newVertexCoordinates
},
    If[TrueQ[OptionValue["AddTerminals"]],
        Return @ ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];
    vertices = VertexList /@ graphs;
    edges = Catenate[EdgeList /@ graphs];
    vertexSize = Association @ Catenate[AnnotationValue[#, VertexSize] & /@ graphs](*MapThread[
  Function[{vs,size},#\[Rule]{1,size}&/@vs],{vertices,1/Normalize[
  procHeight/@{ps},Max]}]*);
    vertexCoordinates = AnnotationValue[#, VertexCoordinates] & /@ graphs;
    vertexXShifts = Most @ FoldList[
        #1 + Max[#2] + 1 + OptionValue["ParallelComposeDistance"] &,
        0,
        vertexCoordinates[[All, All, 1]]
    ];
    vertexYShifts = Map[- Mean[#] &, vertexCoordinates[[All, All, 2]]];
    vertexCoordinateShifts = Thread[{vertexXShifts, vertexYShifts}];
    newVertexCoordinates = Association @ Catenate @
        MapThread[Function[{vs, coords, shift},
            MapThread[#1 -> (#2 + shift )(*vertexSize[#1]*)&, {vs, coords}]],
            {vertices, vertexCoordinates, vertexCoordinateShifts}
        ];
    Graph[Catenate @ vertices, edges,
        VertexCoordinates -> newVertexCoordinates,
        VertexSize -> Normal @ vertexSize,
        VertexShapeFunction -> Catenate[AnnotationValue[#, VertexShapeFunction] & /@ graphs]
    ]
]

ProcGraph[p : Proc[Defer[Composition[ps__Proc]], in_, out_, ___], opts : OptionsPattern[]] := Module[{
    graphs = Map[ProcGraph[#, "AddTerminals" -> False, opts] &, {ps}],
    vertices, edges,
    inBetweenEdges, allEdges,
    outArities, inArities,
    vertexCoordinates,
    vertexXShifts, vertexYShifts, vertexCoordinateShifts,
    widths, arities, minArities, vertexSize,
    newVertexCoordinates
},
    If[TrueQ[OptionValue["AddTerminals"]], 
        Return @ ProcGraph[withTerminals[p], "AddTerminals" -> False, opts]
    ];
    vertices = VertexList /@ graphs;
    edges = Catenate[EdgeList /@ graphs];
    vertexCoordinates = AnnotationValue[#, VertexCoordinates] & /@ graphs;
    vertexXShifts = Map[- Mean[#] &, vertexCoordinates[[All, All, 1]]];
    vertexYShifts = Most @ FoldList[
        #1 + Min[#2] - 1 - OptionValue["ComposeDistance"] &, 
        0,
        vertexCoordinates[[All, All, 2]]
    ];
    vertexCoordinateShifts = Thread[{vertexXShifts, vertexYShifts}];
    inBetweenEdges = Catenate[Apply[betweenEdges] /@ Partition[{ps}, 2, 1]];
    allEdges = Join[edges, inBetweenEdges];
    outArities = GroupBy[allEdges, First, Length];
    inArities = GroupBy[allEdges, #[[2]] &, Length];
    widths = procWidth /@ {ps};
    arities = Total[Map[Max[inArities[#], outArities[#]] /. _Missing -> 0 &, #]] & /@ vertices;
    minArities = Min[Map[Max[inArities[#], outArities[#]] /. _Missing -> 0 &, #]] & /@ vertices;
    vertexSize = Association @ MapThread[
        Function[{vs, minArity, totalArity, sizes, width}, 
            MapThread[Function[{v, size},
                With[{(*arity = Max[inArities[v], outArities[v]] /. _Missing -> 0*)},
                    v -> {size[[1]](*width  Max[arity,1]/Max[minArity, 1]*) (*+(width-1)OptionValue["ParallelComposeDistance"]*), 1}]],
                {vs, sizes}
            ]
      ],
      {vertices, minArities, arities, Values[AnnotationValue[#, VertexSize] & /@ graphs], 1 / Normalize[widths, Max]}];
    newVertexCoordinates = Association @ Catenate @ MapThread[
        Function[{vs, coords, shift}, 
            MapThread[#1 -> (#2 + shift )(*vertexSize[#1]*)&, {vs, coords}]
        ],
        {vertices, vertexCoordinates, vertexCoordinateShifts}
    ];
    Graph[Catenate @ vertices, allEdges,
        VertexCoordinates -> newVertexCoordinates,
        VertexSize -> Normal@vertexSize,
        VertexShapeFunction -> Catenate @ Map[AnnotationValue[#, VertexShapeFunction] &, graphs],
        EdgeShapeFunction -> Map[Function[e,
            With[{i = e[[-1, 1, 1]], j = e[[-1, 1, 2]], v = e[[1]], w = e[[2]]},
                With[{
                    fromShift = {edgeSideShift[i, vertexSize[v], outArities[v]], 1 / 2},
                    toShift = {edgeSideShift[j, vertexSize[w], inArities[w]], - 1 / 2},
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
