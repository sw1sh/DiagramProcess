Package["DiagramProcess`"]

PackageExport["DiagramProcess"]

PackageExport["ProcessTrace"]


Options[DiagramProcess] = {}

DiagramProcess[p_Proc, ___]["Properties"] = {"Process", "Diagram", "Graph"}

DiagramProcess[p_Proc, ___]["Process"] := p

DiagramProcess[p_Proc, ___]["Diagram" | "Graph", opts : OptionsPattern[ProcGraph]] :=
    ProcGraph[p, opts, "AddTerminals" -> True]


DiagramProcess[p_Proc, ___][x___] := p[x]


DiagramProcess[expr : Except[_Proc | _List], opts : OptionsPattern[]] :=
    DiagramProcess[Proc[expr], opts]


DiagramProcess[boxNames_List, opts : OptionsPattern[]] := DiagramProcess[boxNamesProc[boxNames], opts]


DiagramProcess["Identity" | "Id" | "\[Delta]", a_, opts : OptionsPattern[]] :=
    DiagramProcess[identityProc[a], opts]

DiagramProcess["Cap" | "\[Intersection]" | "\[Cap]", a_, opts : OptionsPattern[]] :=
    DiagramProcess[capProc[a], opts]

DiagramProcess["Cup" | "\[Union]" | "\[Cup]", a_, opts : OptionsPattern[]] :=
    DiagramProcess[cupProc[a], opts]

DiagramProcess["Permutation", perm_Cycles, in_List, opts : OptionsPattern[]] :=
    DiagramProcess[permutationProc[perm, in], opts]

DiagramProcess["Swap", a_, b_, opts : OptionsPattern[]] :=
    DiagramProcess[swapProc[a, b], opts]

DiagramProcess["Copy", a_, opts : OptionsPattern[]] :=
    DiagramProcess[copyProc[a], opts]


DiagramProcess /: p_DiagramProcess @* q_DiagramProcess := DiagramProcess[p["Process"] @* q["Process"],
    Sequence @@ Normal @ Merge[{Options[p], Options[q]}, First]]


DiagramProcess /: CircleTimes[p_DiagramProcess, q_DiagramProcess] := DiagramProcess[CircleTimes[p["Process"], q["Process"]],
    Sequence @@ Normal @ Merge[{Options[p], Options[q]}, First]]


DiagramProcess /: Transpose[p : _DiagramProcess] := DiagramProcess[transposeProc @ p["Process"], Sequence @@ Options[p]]


ProcessTrace[p : _DiagramProcess, n_Integer : 1, m_Integer : 1] := DiagramProcess[traceProc[p["Process"], n, m], Sequence @@ Options[p]]

DiagramProcess /: Tr[p : _DiagramProcess] := ProcessTrace[p]


DiagramProcess /: MakeBoxes[DiagramProcess[p_Proc, opts : OptionsPattern[]], form_] := Module[{
    above, below
},
    above = {
        {BoxForm`SummaryItem[{"Process: ", TraditionalForm[getLabel[p] /. Composition -> SmallCircle]}], SpanFromLeft},
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
