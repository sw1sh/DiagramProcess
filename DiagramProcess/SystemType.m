Package["DiagramProcess`"]

PackageExport["SystemType"]

PackageScope["dualTypeQ"]
PackageScope["dualTypesQ"]
PackageScope["dualType"]
PackageScope["typeArity"]


SystemType::usage = "A representation of types for process inputs and outputs"

Options[SystemType] = {"Dual" -> False};

SystemType[type_] := SystemType[type, Sequence @@ Options[SystemType]]

SystemType[CircleTimes[ts__]] := CircleTimes @@ Map[SystemType, {ts}]

SystemType /: (t : CircleTimes[__SystemType]) := SystemType[Defer[t]]

SystemType[SuperStar[type_], opts : OptionsPattern[]] := SuperStar[SystemType[type]]

SystemType /: SuperStar[t_SystemType] := dualType @ t

SystemType[t_SystemType] := t

SystemType[SystemType[t_, ___], args__] := SystemType[t, args]


typeLabel[type : SystemType[t_, ___]] := If[dualTypeQ[type], SuperStar[getLabel[t]], getLabel[t]]

typeLabel[SystemType[Defer[CircleTimes[t_SystemType, t_SystemType]], ___]] := OverHat[typeLabel[t]]


dualTypeQ[SystemType[_, opts : OptionsPattern[]]] :=
    TrueQ[OptionValue[SystemType, opts, "Dual"]]


dualType[SystemType[t : Except[_Defer], opts : OptionsPattern[SystemType]]] :=
    SystemType[t,
      "Dual" -> Not[OptionValue[SystemType, opts, "Dual"]],
      Sequence @@ FilterRules[opts, Except["Dual"]]]

dualType[SystemType[Defer[CircleTimes[ts__]] | Labeled[Defer[CircleTimes[ts__]], _], ___]] := Apply[CircleTimes, dualType /@ {ts}]


typeArity[_SystemType] := 1

typeArity[SystemType[Defer[CircleTimes[ts__]] | Labeled[Defer[CircleTimes[ts__]], _], ___]] := Total[typeArity /@ {ts}]


dualTypesQ[SystemType[Defer[CircleTimes[ts__]] | Labeled[Defer[CircleTimes[ts__]], _], ___]] := dualTypeQ /@ {ts}

dualTypesQ[t_SystemType] := {dualTypeQ[t]}


(* Boxes *)
MakeBoxes[type : SystemType[_, OptionsPattern[]], form_] :=
    ToBoxes[
        Tooltip[
            typeLabel[type],
            Row[{typeLabel[type], ":", If[dualTypeQ[type], SuperStar["Type"], "Type"]}]
        ],
    form]
