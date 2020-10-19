Package["DiagramProcess`"]

PackageExport["SystemType"]

PackageScope["backwardTypeQ"]
PackageScope["reverseType"]


SystemType::usage = "A representation of types for process inputs and outputs"

Options[SystemType] = {"Backward" -> False};

SystemType[type_] := SystemType[type, Sequence @@ Options[SystemType]]

SystemType[CircleTimes[ts__]] := With[{t = CircleTimes @@ Map[SystemType, {ts}]}, SystemType[Defer[t]]]

SystemType[OverBar[type_], opts : OptionsPattern[]] := reverseType @ SystemType[type]

SystemType[t : SystemType[__]] := t


backwardTypeQ[SystemType[_, opts : OptionsPattern[]]] :=
    OptionValue[SystemType, opts, "Backward"]

reverseType[SystemType[t_, opts : OptionsPattern[SystemType]]] :=
    SystemType[t,
      "Backward" -> Not[OptionValue[SystemType, opts, "Backward"]],
      Sequence @@ FilterRules[opts, Except["Backward"]]]


(* Boxes *)
MakeBoxes[SystemType[type_, opts : OptionsPattern[]], form_] :=
    With[{backwardQ =
        TrueQ[OptionValue[SystemType, {opts}, "Backward"]]},
      ToBoxes[Tooltip[If[backwardQ, OverBar[type], type],
        Row[{type, ":", If[backwardQ, OverBar["Type"], "Type"]}]], form]
    ]
