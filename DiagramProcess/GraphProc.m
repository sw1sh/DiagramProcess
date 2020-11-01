Package["DiagramProcess`"]

PackageExport["GraphProc"]



Options[GraphProc] = {Method -> "TopDown"}

GraphProc::unknownMethod = "Method should be one of \"TopDown\" or \"BottomUp\""

GraphProcOptionsCheck[opts : OptionsPattern[GraphProc]] := If[! MatchQ[OptionValue[GraphProc, {opts}, Method], "TopDown" | "BottomUp"], Message[GraphProc::unknownMethod]; False, True]

GraphProc[g_Graph, opts : OptionsPattern[]] /; GraphProcOptionsCheck[opts] :=
    stripTypeSubsripts @ withUniqueTypes[graphProc[#, TrueQ[OptionValue[Method] == "TopDown"]] &, cupifyProcGraph @ g]


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


stripTypeSubsripts[expr : _SystemType | _Proc] := expr /. SystemType[Subscript[t_, _], args___] :> SystemType[t, args]


removeCycles[g_Graph] := Module[{
    loops, cycles, counts
},
    loops = EdgeList[g, DirectedEdge[x_, x_, ___]];
    cycles = FindCycle[If[Length[loops] > 0, EdgeDelete[g, loops], g], Infinity, All];
    counts = Counts[Catenate @ cycles];
    Join[loops, DeleteDuplicates[First @* MaximalBy[counts] /@ cycles]]
]


cupifyProcGraph[g_Graph] := Module[{
    loops, loopEdges, cups, cupEdges, caps, capEdges
},
    loops = EdgeList[g, DirectedEdge[x_, x_, ___]];
    loopEdges = Map[With[{cap = capProc[ #[[ 1, 3, #[[3, 1]] ]] ], cup = cupProc[ #[[ 1, 2, #[[3, 2]] ]] ]}, {
            DirectedEdge[#[[1]], cap, #[[3, 1]] -> 2],
            DirectedEdge[cup, #[[1]], 2 -> #[[3, 1]]],
            DirectedEdge[cup, cap, 1 -> 1]
        }] &,
        loops];
    caps = EdgeList[g, DirectedEdge[_, _, _UpArrow]];
    capEdges = Map[With[{cap = capProc[ #[[ 1, 3, #[[3, 1]] ]] ]}, {
            DirectedEdge[#[[1]], cap, #[[3, 1]] -> 2],
            DirectedEdge[#[[2]], cap, #[[3, 2]] -> 1]
        }] &,
        caps];
    cups = EdgeList[g, DirectedEdge[_, _, _DownArrow]];
    cupEdges = Map[With[{cup = cupProc[ #[[ 1, 2, #[[3, 1]] ]] ]}, {
            DirectedEdge[cup, #[[1]], 2 -> #[[3, 1]]],
            DirectedEdge[cup, #[[2]], 1 -> #[[3, 2]]]
        }] &,
        cups];
    EdgeAdd[EdgeDelete[g, Join[loops, caps, cups]],
        Catenate @ Join[loopEdges, capEdges, cupEdges]
    ]
]


boxNamesProc[boxes_List, opts : OptionsPattern[graphProc]] := Module[{procs, ins, outs, types, edges},
    procs = Proc /@ boxes;
    ins = #[[2]] & /@ procs;
    outs = #[[3]] & /@ procs;
    types = Union @ Flatten @ Join[ins, outs];
    edges = Catenate @ Values @ Merge[{Merge[#[[1]] -> Position[ins, #] & /@ types, Apply[Join]], Merge[#[[1]] -> Position[outs, #] & /@ types, Apply[Join]]}, Apply[
        Join[
            If[Length[#1] > 1,
                Apply[Function[DirectedEdge[procs[[#1[[1]]]], procs[[#2[[1]]]], DownArrow[#1[[2]], #2[[2]]]]]] /@ Partition[#1, 2, 1],
                {}
            ],
            If[Length[#2] > 1,
                Apply[Function[DirectedEdge[procs[[#1[[1]]]], procs[[#2[[1]]]], UpArrow[#1[[2]], #2[[2]]]]]] /@ Partition[#2, 2, 1],
                {}
            ],
            Apply[DirectedEdge[procs[[#1[[1]]]], procs[[#2[[1]]]], Rule[#1[[2]], #2[[2]]]] &] /@ Tuples[{#2, #1}]
        ]
    &]];
    GraphProc[Graph[procs, edges], opts]
]

