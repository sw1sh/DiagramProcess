Package["DiagramProcess`"]

PackageExport["SystemType"]

PackageScope["dualTypeQ"]
PackageScope["dualTypesQ"]
PackageScope["dualType"]
PackageScope["typeArity"]
PackageScope["typeDimensions"]
PackageScope["typeBasis"]


SystemType::usage = "A representation of types for process inputs and outputs"

Options[SystemType] = {"Dual" -> False, "Dimensions" -> {2}, "Field" -> Complexes};

SystemType[type : Except[_SystemType]] := SystemType[type, Sequence @@ Options[SystemType]]

SystemType[type : Except[_SystemType], opts : OptionsPattern[]] /; ! ContainsAll[Keys[{opts}], Keys[Options[SystemType]]] :=
    SystemType[type, opts, Sequence @@ FilterRules[Options[SystemType], Except[{opts}]]]

SystemType[CircleTimes[ts__], opts : OptionsPattern[]] := CircleTimes @@ Map[SystemType[#, opts] &, {ts}]

SystemType /: (t : CircleTimes[ts__SystemType]) := SystemType[Defer[t],
    "Dimensions" -> Catenate[typeDimensions /@ {ts}], "Field" -> Apply[CircleTimes, typeField /@ {ts}]]

SystemType[SuperStar[type_], opts : OptionsPattern[]] := SuperStar[SystemType[type, opts]]

SystemType /: SuperStar[t_SystemType] := dualType @ t


SystemType[SystemType[t_, args1___], args2___] := SystemType[t, Sequence @@ Normal @ Merge[Join[{args2}, {args1}], First]]


typeLabel[type : SystemType[t_, ___]] := If[dualTypeQ[type], SuperStar[getLabel[t]], getLabel[t]]

typeLabel[SystemType[Defer[CircleTimes[t_SystemType, t_SystemType]], ___]] := OverHat[typeLabel[t]]


dualTypeQ[SystemType[_, opts : OptionsPattern[]]] :=
    TrueQ[OptionValue[SystemType, {opts}, "Dual"]]


dualType[SystemType[t : Except[_Defer], opts : OptionsPattern[SystemType]]] :=
    SystemType[t,
      "Dual" -> Not[OptionValue[SystemType, {opts}, "Dual"]],
      Sequence @@ FilterRules[{opts}, Except["Dual"]]]

dualType[SystemType[Defer[CircleTimes[ts__]], ___]] := Apply[CircleTimes, dualType /@ {ts}]


typeArity[_SystemType] := 1

typeArity[SystemType[Defer[CircleTimes[ts__]], ___]] := Total[typeArity /@ {ts}]


dualTypesQ[SystemType[Defer[CircleTimes[ts__]], ___]] := dualTypeQ /@ {ts}

dualTypesQ[t_SystemType] := {dualTypeQ[t]}


typeDimensions[SystemType[_, opts : OptionsPattern[]]] := OptionValue[SystemType, {opts}, "Dimensions"]


typeField[SystemType[_, opts : OptionsPattern[]]] := OptionValue[SystemType, {opts}, "Field"]


typeBasis[t_SystemType] := With[{dims = typeDimensions[t]},
    SparseArray[{IntegerDigits[#, MixedRadix[dims], Length[dims]] + 1 -> 1}, dims] & /@ Range[0, Times @@ dims - 1]
]


(* Boxes *)
MakeBoxes[type : SystemType[_, OptionsPattern[]], form_] := With[{
    boxes = ToBoxes[typeLabel[type], form],
    tooltip = ToBoxes[Superscript[If[dualTypeQ[type], SuperStar[typeField[type]], typeField[type]], CircleTimes @@ typeDimensions[type]], form]
},
    InterpretationBox[
        boxes,
        type,
        Tooltip -> tooltip
    ]
]
