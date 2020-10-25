Package["DiagramProcess`"]

PackageExport["SystemType"]

PackageScope["dualTypeQ"]
PackageScope["dualType"]


SystemType::usage = "A representation of types for process inputs and outputs"

Options[SystemType] = {"Dual" -> False};

SystemType[type_] := SystemType[type, Sequence @@ Options[SystemType]]

SystemType[CircleTimes[ts__]] := CircleTimes @@ Map[SystemType, {ts}]

SystemType /: (t : CircleTimes[__SystemType]) := SystemType[Defer[t]]

SystemType[SuperStar[type_], opts : OptionsPattern[]] := SuperStar[SystemType[type]]

SystemType /: SuperStar[t_SystemType] := dualType @ t

SystemType[t_SystemType] := t

SystemType[SystemType[t_, ___], args__] := SystemType[t, args]


dualTypeQ[SystemType[_, opts : OptionsPattern[]]] :=
    TrueQ[OptionValue[SystemType, opts, "Dual"]]

dualType[SystemType[t_, opts : OptionsPattern[SystemType]]] :=
    SystemType[t,
      "Dual" -> Not[OptionValue[SystemType, opts, "Dual"]],
      Sequence @@ FilterRules[opts, Except["Dual"]]]


(* Boxes *)
MakeBoxes[type : SystemType[t_, opts : OptionsPattern[]], form_] :=
    With[{dualQ = dualTypeQ[type]},
        ToBoxes[
            Tooltip[
                If[dualQ, SuperStar[t], t],
                Row[{t, ":", If[dualQ, SuperStar["Type"], "Type"]}]
            ],
        form]
    ]
