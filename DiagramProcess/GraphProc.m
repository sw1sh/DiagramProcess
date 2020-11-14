Package["DiagramProcess`"]

PackageExport["GraphProc"]



Options[GraphProc] = {Method -> "TopDown"}

GraphProc::unknownMethod = "Method should be one of \"TopDown\" or \"BottomUp\""

GraphProcOptionsCheck[opts : OptionsPattern[GraphProc]] := If[! MatchQ[OptionValue[GraphProc, {opts}, Method], "TopDown" | "BottomUp"], Message[GraphProc::unknownMethod]; False, True]

GraphProc[g_Graph, opts : OptionsPattern[]] /; GraphProcOptionsCheck[opts] :=
    stripTypeDecorations @ withUniqueTypes[graphProc[#, TrueQ[OptionValue[Method] == "TopDown"]] &, cupifyProcGraph @ g]


graphProc[g_Graph, topDown_ : False] := Module[{
    sideLayer,
    restGraph
},
    If[ topDown,

        sideLayer = Select[VertexList[g], VertexOutDegree[g, #] == 0 &];
        restGraph = VertexDelete[g, sideLayer];
        If[ VertexCount[restGraph] > 0,
            With[{proc = graphProc[restGraph, topDown]}, Apply[CircleTimes, SortBy[sideLayer, positionIn[proc[[3]], #[[2]]] &]] @* proc],
            Apply[CircleTimes, sideLayer]
        ],

        sideLayer = Select[VertexList[g], VertexInDegree[g, #] == 0 &];
        restGraph = VertexDelete[g, sideLayer];
        If[ VertexCount[restGraph] > 0,
            With[{proc = graphProc[restGraph, topDown]}, proc @* Apply[CircleTimes, SortBy[sideLayer, positionIn[proc[[2]], #[[3]]] &]]],
            Apply[CircleTimes, sideLayer]
        ]
    ]
]


unifyTypes[g_Graph] := Map[Function[e, With[{i = e[[3, 1]], j = e[[3, 2]]}, e[[1, 3, i]] == e[[2, 2, j]]]], EdgeList[g]]


uniqueTypes[g_Graph] := Module[{
    newGraph, replacements,
    rules
},
    If[VertexCount[g] == 0, Return[{g, {}}]];
    {newGraph, replacements} = Reap @ vertexMap[replaceUnderHold[
        (t : SystemType[Except[_Defer], ___]) :> With[{unique = SystemType[Unique[]]}, Sow[t -> unique]; unique]
        ],
        g
    ];
    rules = ToRules @ Resolve @ unifyTypes @ newGraph;
    newGraph = edgeMap[ReplaceAll[replacements[[1]]], newGraph];
    {graphReplace[newGraph, rules], DeleteDuplicates @ ReplaceAll[replacements[[1]], rules]}
]


withUniqueTypes[f_, graph_Graph] := Module[{
    newGraph, typeReplacements, backwardTypeReplacements
},
    {newGraph, typeReplacements} = uniqueTypes[graph];
    backwardTypeReplacements = Map[Apply[SystemType[#2[[1]], ___] -> #1 &], typeReplacements];
    With[{r = f[newGraph]},
        If[MatchQ[r, _Graph], graphReplace[r, backwardTypeReplacements], ReplaceAll[r, backwardTypeReplacements]]
    ]
]


stripTypeDecorations[expr : _SystemType | _Proc] := expr //. SystemType[(Subscript | Overscript)[t_, _], args___] :> SystemType[t, args]


graphCycles[g_Graph] := Module[{
    loops, cycles, counts
},
    loops = EdgeList[g, DirectedEdge[x_, x_, _Rule]];
    cycles = FindCycle[If[Length[loops] > 0, EdgeDelete[g, loops], g], Infinity, All];
    counts = Counts[Catenate @ cycles];
    Join[List /@ loops, #[[{1, -1}]] & /@ cycles]
]


cupifyProcGraph[g_Graph] := Module[{
    cycles, cycleEdges, cups, cupEdges, caps, capEdges
},
    cycles = Map[SortBy[#[[3, 2]] &]] @ graphCycles[g];
    cycleEdges = Map[With[{cap = capProc[ #[[1, 1, 3, #[[1, 3, 1]] ]] ], cup = cupProc[ #[[-1, 2, 2, #[[2, 3, 2]] ]] ]}, {
            DirectedEdge[#[[-1, 1]], cap, #[[-1, 3, 1]] -> 2],
            DirectedEdge[cup, #[[1, 1]], 2 -> #[[-1, 3, 2]]],
            DirectedEdge[cup, cap, 1 -> 1]
        }] &,
        cycles];
    caps = EdgeList[g, DirectedEdge[_, _, _UpArrow]];
    capEdges = Map[With[{cap = capProc[ #[[ 1, 3, #[[3, 1]] ]] ]}, {
            DirectedEdge[#[[1]], cap, #[[3, 1]] -> 1],
            DirectedEdge[#[[2]], cap, #[[3, 2]] -> 2]
        }] &,
        caps];
    cups = EdgeList[g, DirectedEdge[_, _, _DownArrow]];
    cupEdges = Map[With[{cup = cupProc[ #[[ 1, 2, #[[3, 1]] ]] ]}, {
            DirectedEdge[cup, #[[1]], 1 -> #[[3, 1]]],
            DirectedEdge[cup, #[[2]], 2 -> #[[3, 2]]]
        }] &,
        cups];
    With[{deleteEdges = Join[Last /@ cycles, caps, cups]},
        EdgeAdd[
            If[Length[deleteEdges] > 0, EdgeDelete[g, deleteEdges], g],
            Catenate @ Join[cycleEdges, capEdges, cupEdges]
        ]
    ]
]


boxNamesProc[boxes_List, opts : OptionsPattern[graphProc]] := Module[{
    procs, procTypes, uniqueTypes, edges
},
    procs = Proc /@ boxes;
    procTypes = {procInput[#], procOutput[#]} & /@ procs;
    uniqueTypes = Union @ Flatten @ procTypes;
    edges = Catenate @ KeyValueMap[Function[{type, indices},
        With[{
            n = Count[indices[[All, 2]], 2] + Boole[MatchQ[type[[1]], Overscript[_, ToExpression @ "\[Breve]"]]],
            m = Count[indices[[All, 2]], 1] + Boole[MatchQ[type[[1]], Overscript[_, ToExpression @ "\[DownBreve]"]]]
        },
        With[{
            spider = spiderProc[n, m, type]
        },
            Module[{i = 1, j = 1},
            Map[
                If[ #1[[2]] == 1,
                    DirectedEdge[spider, procs[[#1[[1]]]], i++ -> #1[[3]]],
                    DirectedEdge[procs[[#1[[1]]]], spider, #1[[3]] -> j++]
                ] &,
                indices
            ]
            ]
        ]]
    ],
        Merge[# -> Position[procTypes, #] & /@ uniqueTypes, Apply[Join]]
    ];
    GraphProc[Graph[procs, edges], opts]
]
