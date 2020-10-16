Package["DiagramProcess`"]

PackageExport["DiagramProcess"]


Options[DiagramProcess] = {}

DiagramProcess[p_Proc, ___]["Properties"] = {"Process", "Graph"}

DiagramProcess[p_Proc, ___]["Process"] := p
DiagramProcess[p_Proc, ___]["Graph", opts : OptionsPattern[ProcGraph]] :=
    ProcGraph[p, "AddTerminals" -> True, opts]
DiagramProcess[p_Proc, ___][x___] := p[x]


DiagramProcess[expr : Except[_Proc], opts : OptionsPattern[]] :=
    DiagramProcess[Proc[expr], opts]

DiagramProcess["Identity" | "Id" | "\[Delta]", a_] :=
    DiagramProcess[identityProc[a]]
DiagramProcess["Cap" | "\[Intersection]" | "\[Cap]", a_] :=
    DiagramProcess[capProc[a]]
DiagramProcess["Cup" | "\[Union]" | "\[Cup]", a_] :=
    DiagramProcess[cupProc[a]]

DiagramProcess /: p_DiagramProcess @* q_DiagramProcess :=
    DiagramProcess[p["Process"] @* q["Process"]]
DiagramProcess /: CircleTimes[p_DiagramProcess, q_DiagramProcess] :=
    DiagramProcess[CircleTimes[p["Process"], q["Process"]]]

DiagramProcess /: Transpose[p : _DiagramProcess] := DiagramProcess[transposeProc @ p["Process"]]

DiagramProcess /: MakeBoxes[DiagramProcess[p_Proc, opts : OptionsPattern[]], form_] := Module[{
    above, below
},
    above = {
        {BoxForm`SummaryItem[{"Process: ", getLabel[p]}], SpanFromLeft},
        {BoxForm`SummaryItem[{"Input: ", p[[2]]}], BoxForm`SummaryItem[{"Output: ", p[[3]]}]
        }
    };
    below = {};
    BoxForm`ArrangeSummaryBox[
        DiagramProcess,
        p,
        GraphPlot[ProcGraph[p, "ShowLabels" -> False, "AddTerminals" -> True, "ArrowPosition" -> 0.7], ImageSize -> Tiny],
        above,
        below,
        form,
        "Interpretable" -> Automatic
    ]
]
