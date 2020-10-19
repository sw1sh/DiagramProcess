Package["DiagramProcess`"]

PackageExport["DiagramProcess"]


Options[DiagramProcess] = {}

DiagramProcess[p_Proc, ___]["Properties"] = {"Process", "Diagram", "Graph"}

DiagramProcess[p_Proc, ___]["Process"] := p
DiagramProcess[p_Proc, ___]["Diagram" | "Graph", opts : OptionsPattern[ProcGraph]] :=
    ProcGraph[p, opts, "AddTerminals" -> True]
DiagramProcess[p_Proc, ___][x___] := p[x]


DiagramProcess[expr : Except[_Proc], opts : OptionsPattern[]] :=
    DiagramProcess[Proc[expr], opts]

DiagramProcess["Identity" | "Id" | "\[Delta]", a_, opts : OptionsPattern[]] :=
    DiagramProcess[identityProc[a], opts]
DiagramProcess["Cap" | "\[Intersection]" | "\[Cap]", a_, opts : OptionsPattern[]] :=
    DiagramProcess[capProc[a], opts]
DiagramProcess["Cup" | "\[Union]" | "\[Cup]", a_, opts : OptionsPattern[]] :=
    DiagramProcess[cupProc[a], opts]

DiagramProcess /: p_DiagramProcess @* q_DiagramProcess :=
    DiagramProcess[p["Process"] @* q["Process"]]
DiagramProcess /: CircleTimes[p_DiagramProcess, q_DiagramProcess] :=
    DiagramProcess[CircleTimes[p["Process"], q["Process"]], Sequence @@ Normal @ Merge[{Options[p], Options[q]}, First]]

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
        GraphPlot[ProcGraph[p, opts, "ShowLabels" -> False, "AddTerminals" -> True, "ArrowPosition" -> 0.7], ImageSize -> Tiny],
        above,
        below,
        form,
        "Interpretable" -> Automatic
    ]
]
