Package["DiagramProcess`"]

PackageExport["SystemType"]

PackageScope["dualTypeQ"]
PackageScope["dualTypesQ"]
PackageScope["dualType"]
PackageScope["reverseType"]
PackageScope["typeArity"]
PackageScope["typeDimensions"]
PackageScope["typeBasis"]
PackageScope["typeList"]


SystemType::usage = "A representation of types for process inputs and outputs"

Options[SystemType] = {"Dimensions" -> {2}, "Dual" -> False, "Field" -> Complexes};


SystemType[_, opts : OptionsPattern[]][s_String] /; MemberQ[Keys[Options[SystemType]], s] := OptionValue[SystemType, {opts}, s]

$systemTypeProperties = Join[Keys[Options[SystemType]], {"Arity", "Basis", "Label", "Properties"}]

_SystemType["Properties"] := $systemTypeProperties


SystemType[type : Except[_SystemType]] := SystemType[type, Sequence @@ Options[SystemType]]

SystemType[type : Except[_SystemType], opts : OptionsPattern[]] /; ! ContainsAll[Keys[{opts}], Keys[Options[SystemType]]] :=
    SystemType[type, opts, Sequence @@ FilterRules[Options[SystemType], Except[{opts}]]]

SystemType[CircleTimes[ts__], opts : OptionsPattern[]] := CircleTimes @@ Map[SystemType[#, opts] &, {ts}]

SystemType /: (t : CircleTimes[ts__SystemType]) := SystemType[Defer[t],
    "Dimensions" -> Catenate[typeDimensions /@ {ts}], "Field" -> Apply[CircleTimes, typeField /@ {ts}]]

SystemType[SuperStar[type_], opts : OptionsPattern[]] := SuperStar[SystemType[type, opts]]

SystemType[(Power | Superscript | Overscript)[type_, n_Integer], opts : OptionsPattern[]] := SystemType[type,
    Sequence @@ SortBy[Append[FilterRules[{opts}, Except["Dimensions"]], "Dimensions" -> {n}], First]
]

SystemType /: SuperStar[t_SystemType] := dualType @ t


SystemType[SystemType[t_, args1___], args2___] := SystemType[t, Sequence @@ Normal @ Merge[Join[{args2}, {args1}], First]]


typeLabel[type : SystemType[t_, ___]] := If[dualTypeQ[type], SuperStar[getLabel[t]], getLabel[t]]

typeLabel[SystemType[Defer[CircleTimes[s_SystemType, t_SystemType]], ___]] /; s === dualType[t] := OverHat[typeLabel[t]]

t_SystemType["Label"] := typeLabel[t]


dualTypeQ[t_SystemType] := TrueQ[t["Dual"]]


dualType[SystemType[t : Except[_Defer], opts : OptionsPattern[SystemType]]] :=
    SystemType[t,
      Sequence @@ SortBy[Append[FilterRules[{opts}, Except["Dual"]], "Dual" -> Not[OptionValue[SystemType, {opts}, "Dual"]]], First]
    ]

dualType[SystemType[Defer[CircleTimes[ts__]], ___]] := Apply[CircleTimes, dualType /@ {ts}]


reverseType[SystemType[Defer[CircleTimes[ts__]], ___]] := CircleTimes @@ Reverse[{ts}]

reverseType[t_SystemType] := t


typeArity[_SystemType] := 1

typeArity[SystemType[Defer[CircleTimes[ts__]], ___]] := Total[typeArity /@ {ts}]

t_SystemType["Arity"] := typeArity[t]


dualTypesQ[SystemType[Defer[CircleTimes[ts__]], ___]] := dualTypeQ /@ {ts}

dualTypesQ[t_SystemType] := {dualTypeQ[t]}


typeDimensions[t_SystemType] := t["Dimensions"]


typeField[t_SystemType] := t["Field"]


typeList[SystemType[Defer[CircleTimes[ts__SystemType]], ___]] := Catenate[typeList /@ {ts}]

typeList[t : SystemType[Except[_Defer], ___]] := {t}


typeBasis[t_SystemType, matrix_ : False, flatten_ : True] := Module[{
    dims = typeDimensions[t],
    basis
},
    basis = Array[SparseArray[{{##} -> 1}, dims] &, dims];
    If[ TrueQ[matrix],
        basis = ArrayReshape[#, {1, Times @@ dims}] & /@ basis
    ];
    If[TrueQ[flatten], Flatten[basis, Length[dims] - 1], basis]
]

t_SystemType["Basis", args___] := typeBasis[t, args]


(* Boxes *)
MakeBoxes[type : SystemType[_, OptionsPattern[]], form_] := With[{
    boxes = ToBoxes[typeLabel[type], form],
    tooltip = ToBoxes[unWrap[MapThread[Superscript, {wrap[typeField[type] /. CircleTimes -> List], typeDimensions[type]}]] /. List -> CircleTimes, form]
},
    InterpretationBox[
        boxes,
        type,
        Tooltip -> tooltip
    ]
]
