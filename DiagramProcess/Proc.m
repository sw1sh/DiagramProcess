Package["DiagramProcess`"]

PackageExport["Proc"]

PackageScope["procFunc"]
PackageScope["procInput"]
PackageScope["procOutput"]
PackageScope["procTags"]
PackageScope["procLabel"]
PackageScope["procTagQ"]


Options[Proc] = {};

(*Construction*)

Proc[Subsuperscript[f_, Row[As_], Row[Bs_]]] :=
    Proc[f, SystemType /@ As, SystemType /@ Bs, {}]

Proc[Subsuperscript[f_, A_, Bs_Row]] :=
    Proc[Subsuperscript[f, Row @ wrap @ A, Bs]]

Proc[Subsuperscript[f_, As_Row, B_]] :=
    Proc[Subsuperscript[f, As, Row @ wrap @ B]]

Proc[Subsuperscript[f_, A_, B_]] :=
    Proc[Subsuperscript[f, Row @ wrap @ A, Row @ wrap @ B]]

Proc[Subscript[f_, A_]] := Proc[Subsuperscript[f, A, {}]]

Proc[Superscript[f_, B_]] := Proc[Subsuperscript[f, {}, B]]

Proc[Underoverscript[f_, A_, B_]] := Proc[Subsuperscript[f, A, B]]

Proc[Underscript[f_, A_]] := Proc[Subscript[f, A]]

Proc[Overscript[f_, B_]] := Proc[Superscript[f, B]]

Proc[Power[f_, Bs_]] := Proc[Superscript[f, Bs]]

Proc[Power[Subscript[f_, As_], Bs_]] := Proc[Subsuperscript[f, As, Bs]]


Proc[Transpose[f_]] := transposeProc @ Proc[f]


Proc[SuperDagger[f_]] := adjointProc @ Proc[f]


Proc[OverBar[f_]] := conjugateProc @ Proc[f]


Proc[Tr[f_]] := traceProc @ Proc[f]


Proc[1, {in_}, {out_}, ___] := If[in === out, identityProc[in], castProc[in, out]]


Proc[1] := emptyProc[]


Proc[0] := zeroProc[]


Proc[p_Proc] := p


Proc /: (Composition | SmallCircle)[ps__Proc] :=
    flattenProc @ Fold[composeProcs, Map[Proc, {ps}]]


Proc /: CircleTimes[p_Proc] := p
Proc /: CircleTimes[ps__Proc] :=
    flattenProc @
        Proc[Defer[CircleTimes[ps]], Catenate[#[[2]] & /@ {ps}],
          Catenate[#[[3]] & /@ {ps}], {"parallel composition"}]


Proc /: Plus[ps__Proc] :=
    flattenProc @
        Proc[Defer[Plus[ps]], {ps}[[1, 2]], {ps}[[1, 3]], {"plus"}]


Proc /: Transpose[p_Proc] := transposeProc @ p


Proc /: SuperDagger[p_Proc] := adjointProc @ p


Proc /: OverBar[p_Proc] := conjugateProc @ p


Proc[p : _Composition | _SmallCircle | _CircleTimes | _Plus] := Map[Proc, p]

Proc[Sum[p_, i_]] := CircleTimes[sumProc[i], Proc[p]]


Proc[f : Except[_Subsuperscript | _Superscript | _Subscript |
    _Underoverscript | _Underscript | _Overscript | _Power | _Composition |
    _CircleTimes | _SmallCircle | _Plus]] := Proc[Subsuperscript[f, {}, {}]]


procFunc[Proc[f_, ___]] := Replace[f, Labeled[g_, _] :> g]


procLabel[Proc[Defer[Composition[ps__]], __]] := SmallCircle @@ Map[procLabel, {ps}]

procLabel[Proc[Defer[CircleTimes[ps__]], __]] := CircleTimes @@ Map[procLabel, {ps}]

procLabel[Proc[Defer[Plus[ps__]], __]] := Plus @@ Map[procLabel, {ps}]

procLabel[Proc[f_, __]] := getLabel[f]


procInput[Proc[_, in_, ___]] := in


procOutput[Proc[_, _, out_, ___]] := out


procTags[p_Proc] := p[[4]]


procTagQ[p_Proc, ps_List] := AllTrue[ps, procTagQ[p, #] &]

procTagQ[p_Proc, patt_] := AnyTrue[procTags[p], MatchQ[patt]]

procTagQ[patt_] := Function[p, procTagQ[p, patt]]


(* Eval Proc *)

Proc::typeSizeMissmatch =
    "Number of inputs `1` doesn't match number of outputs `2`. Padding with Missing[]";

Proc[Defer[Composition[p_Proc, ps___Proc]], in_, out_, args___][x___] := With[{
  q = Proc[Defer[Composition[ps]], in, p[[2]], args]
},
    With[{y = q @@ PadRight[{x}, Length @ in, Missing["Input", procLabel[q]]]},
      p @@ PadRight[y, Length[p[[2]]], Missing["Output", procLabel[q]]]]
]

(p : Proc[Defer[CircleTimes[ps___Proc]], in_, out_, ___])[x___] :=
    Catenate @ Parallelize[MapThread[
      wrap[#1 @@ #2] &, {
        {ps},
        TakeList[PadRight[{x}, Length @ in, Missing["Input", procLabel[p]]],
            Length /@ Values[procIn[p]]]
        }
    ], DistributedContexts -> Automatic]

(p : Proc[Except[Defer[_Composition | _CircleTimes | _Plus]], in_, out_, ___])[x___] := Module[{
  input, output
},
    input = PadRight[{x}, Length[in], Missing["Input", procLabel[p]]];
    output = wrap[unProc[p] @@ input];
    PadRight[output, Length[out], Missing["Output", procLabel[p]]]
]


(* Boxes *)

Proc /: MakeBoxes[p : Proc[f_, A_List, B_List, _, ___], form_] := With[{
    label = procLabel[p] /. "Transpose"[l_] :> Transpose[l]
},
    ToBoxes[
        Tooltip[
            Underoverscript[
                If[ MatchQ[label, _SmallCircle | _CircleTimes | _Plus], Row[{"(", label, ")"}], label],
                Row @ A, Row @ B
            ],
        Row[{"Proc", ":", If[Length[A] == 0, "*", Splice @ A], "\[Rule]", If[Length[B] == 0, "*", Splice @ B]}]
        ],
        TraditionalForm
    ]
]
