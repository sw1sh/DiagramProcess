Package["DiagramProcess`"]

PackageExport["DiagramProcess"]

PackageExport["ProcessTrace"]


Options[DiagramProcess] = {"Simplify" -> False, "Double" -> None}


DiagramProcess[p_Proc, ___]["Properties"] = {"Process", "Diagram", "Graph", "Tensor"}


DiagramProcess[p_Proc, OptionsPattern[]]["Process"] := If[OptionValue["Double"] === None,
    p,
    If[TrueQ[OptionValue["Double"]], doubleProc @ p, unDoubleProc @ p]
]


(d : DiagramProcess[_, opts : OptionsPattern[]])["Diagram" | "Graph", gopts : OptionsPattern[ProcGraph]] := With[{
    g = ProcGraph[d["Process"], gopts]
},
    If[TrueQ[OptionValue["Simplify"]], simplifyProcGraph @ g, g]
]


d_DiagramProcess["Tensor"] := ProcTensor[d["Process"]]


DiagramProcess[p_Proc, ___][x___] := p[x]


DiagramProcess[d_DiagramProcess, args___] := DiagramProcess[d["Process"], args]


DiagramProcess[boxNames_List, opts : OptionsPattern[]] := DiagramProcess[boxNamesProc[boxNames], opts]


DiagramProcess[name_String, opts : OptionsPattern[]] := DiagramProcess[Proc[name], opts]

DiagramProcess[name_String[args___], opts : OptionsPattern[]] := DiagramProcess[Proc[name[args]], opts]


DiagramProcess[fs : HoldPattern[Plus[Except[_Proc] ..]], opts : OptionsPattern[]] := DiagramProcess[Map[Proc, fs], opts]

DiagramProcess[HoldPattern[Sum[f : Except[_Proc], i_]], opts : OptionsPattern[]] := DiagramProcess[Sum[Proc[f], i], opts]


DiagramProcess[expr : Except[_DiagramProcess | _Proc | _List | _String | _Graph], opts : OptionsPattern[]] :=
    DiagramProcess[Proc[expr], opts]


DiagramProcess /: Composition[ps__DiagramProcess] := DiagramProcess[Composition @@ Map[#["Process"] &, {ps}],
    Sequence @@ Normal @ Merge[FilterRules[Options[#], Options[ProcGraph]] & /@ {ps}, First]]


DiagramProcess /: CircleTimes[ps__DiagramProcess] := DiagramProcess[CircleTimes @@ Map[#["Process"] &, {ps}],
    Sequence @@ Normal @ Merge[FilterRules[Options[#], Options[ProcGraph]] & /@ {ps}, First]]


DiagramProcess /: Transpose[p : _DiagramProcess] := DiagramProcess[transposeProc @ p["Process"], Sequence @@ Options[p]]

DiagramProcess /: SuperDagger[p : _DiagramProcess] := DiagramProcess[adjointProc @ p["Process"], Sequence @@ Options[p]]

DiagramProcess /: OverBar[p : _DiagramProcess] := DiagramProcess[conjugateProc @ p["Process"], Sequence @@ Options[p]]

DiagramProcess /: Plus[ps__DiagramProcess] := DiagramProcess[Plus @@ Map[#["Process"] &, {ps}], Sequence @@ Options[First @ {ps}]]

DiagramProcess /: Sum[p_DiagramProcess, i_] := DiagramProcess[Sum[p["Process"], i], Sequence @@ Options[p]]


ProcessTrace[p : _DiagramProcess, n_Integer : 1, m_Integer : 1] := DiagramProcess[traceProc[p["Process"], n, m], Sequence @@ Options[p]]

DiagramProcess /: Tr[p : _DiagramProcess] := ProcessTrace[p]


DiagramProcess /: Equal[a_DiagramProcess, b_DiagramProcess] := ContainsExactly[
    EdgeList @ simplifyProcGraph[a["Diagram"]],
    EdgeList @ simplifyProcGraph[b["Diagram"]]
]


DiagramProcess[g_Graph, opts : OptionsPattern[]] /; AllTrue[VertexList[g], MatchQ[_Proc]] := DiagramProcess[GraphProc[g], opts]


DiagramProcess /: MakeBoxes[d : DiagramProcess[_, opts : OptionsPattern[]], form_] := Module[{
    p = d["Process"],
    above, below
},
    above = {
        {BoxForm`SummaryItem[{"Process: ", TraditionalForm[procLabel[p] /. "Transpose"[l_] :> Transpose[l]]}], SpanFromLeft},
        {BoxForm`SummaryItem[{"Input: ", p[[2]]}], BoxForm`SummaryItem[{"Output: ", p[[3]]}]
        }
    };
    below = {};
    BoxForm`ArrangeSummaryBox[
        DiagramProcess,
        d,
        Magnify[Plus @@ wrap @ d[
            "Diagram",
            Sequence @@ FilterRules[{opts}, Options[ProcGraph]], "ShowWireLabels" -> False, "AddTerminals" -> True, "ArrowPosition" -> 0.7
        ], 0.5],
        above,
        below,
        form,
        "Interpretable" -> Automatic
    ]
]
