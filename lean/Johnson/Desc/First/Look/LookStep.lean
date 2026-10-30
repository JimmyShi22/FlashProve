-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookStep.lean: the step of a proof file's decision that hears the messages
of a lookup. Definitions with code. No theorem.

What is heard, and how, is `lkPad` (OnBytes/K/Kc/FlatHear.lean), the program's routine
`Forest.pad` (OnBytes/Model/Look.lean:369-421) line for line as a function on a sub-proof's ledger
and a tape of rounds, over the masked sumcheck in the same form (OnBytes/K/Kc/Flat.lean). What this
file adds is the way from a view's rounds and the plan's entries to that tape, and it is STRICT: the
maker `paired` (OnBytes/K/Kc/Laws.lean:63) was made for a law in one direction
and lets by what the program's channel refuses.

Main names:
  `elemsOf`: a message's items as elements of the extension field; nothing if one is of another
    kind.
  `kindAsked`, `roundS r e`: a view's round with its entry in the plan as a `FlatRound`, or nothing.
  `tapeS rs es`: the stretch's rounds with the stretch's entries, one for one, or nothing.
  `lookRun`: **the lookup's messages**: from the three public arguments, the stretch's entries, the
    ledger and the stretch's rounds to what was heard and the ledger behind; nothing is left over.
  `lookStep`: the same in the form of a step of a chain's decision: from a state, the stretch's
    rounds and the opened columns not yet taken to a state and the number of columns taken: 0.

Limits: it hears; it tests no equation: every sumcheck leaves a claim, as a form in what is
returned; a sent value that is changed is refused nowhere here. Of an entry it does not read count,
work, msg, roots, answers and logN. That the entry closed last before the stretch owes no question
is the matter of the step in front. That an element which the plan draws other than 0 is not 0 is
not tested, here or in the program. What a round draws has a fourth part, a digest: neither the
program's close nor this file reads it. Where a clause of `roundS` fails the whole stretch is
refused before a round is heard: the decision is the program's, the place of the refusal is not.
Nothing has been shown of it.

THE GUARDS. A row: the program's file:line · where it stands here · class (V: a turned view can trip
it; P: a turned plan or public number can; T: no input can).
  Ground.lean:770 no round is left, at an item · Flat.lean:92 (recv on the empty tape) · V
  Ground.lean:773 no item is left in the round · Flat.lean:92 (recv, second arm) · V
  Ground.lean:781 an item of another kind is taken · elemsOf, third arm · V
  Ground.lean:841 no item unread · elemsOf, with Flat.lean:108-116 (sent = []) · V
  Ground.lean:841 drawn.elems.length = e.drawE · roundS, clause 1 · V, P
  Ground.lean:841 drawn.poss.length = e.poss, and Rounds.lean:96 e.poss = 0 · clause 2 · V, P
  Ground.lean:842 drawn.trits.length = e.trits, and Rounds.lean:96 e.trits = the call's number of
    matrix entries, which is 0 in each of the four closes that a lookup calls · clause 3 · V, P
  Ground.lean:825 settled: no routine of a lookup asks for rows, so none may be owed · clause 4 · P
  Rounds.lean:108 noBatching · clause 5 · T there; here see below
  Rounds.lean:93 the format's kind of the name is the call's · clause 6, with kindAsked · T there
    (the program's two stand on the call's name, these on the entry's: a turned plan can trip them,
    but never alone: the name's guard refuses the same input: no control of their own)
  Ground.lean:823, :839 no entry, no round is left, at a close · Flat.lean:111, :116 (closeN,
    closeOne on the empty tape); tapeS's last arm makes the two lists equally long · V, P
  Ground.lean:825 the entry's name and drawNZ · Flat.lean:108-116 · P
  Rounds.lean:96 e.drawE = the call's number · Flat.lean:108-116, with clause 1 · P
  the run's end: entries and rounds used up · lookRun, the pattern [] · V, P
  Look.lean:370, :371 · FlatHear.lean:108, :109 · P
  Look.lean:393, :408, :410, :412-413 · FlatHear.lean:129, :140, :141, :143-144 · T

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Kc.FlatHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Call)

/-- A message's items as elements of the extension field; nothing if one is of another kind. -/
def elemsOf : List Fmt.ItemValue → Option (List E)
  | [] => some []
  | .e x :: l => (elemsOf l).map (E.ofTriple x :: ·)
  | _ :: _ => none

/-- The kind under which the program's routines close a round of this name in a lookup: `trAnswer`,
`trAnswerNotZero`, `trPoint`, `trEmpty` (OnBytes/Model/Rounds.lean:143-171). -/
def kindAsked (name : String) : Fmt.Kind :=
  if name == Model.RoundName.pscEpsilon.name then .join
  else if name == Model.RoundName.pscValues.name then .nothing
  else .elems

/-- A view's round with its entry in the plan, as plain data. Nothing unless every item is an
element, as many elements are drawn as the entry says, neither has a position or a matrix entry, the
entry batches no row, its name is not that of the round that batches rows, and the format gives the
name the kind under which the program closes it. -/
def roundS (r : Fmt.RoundView) (e : Fmt.Entry) : Option FlatRound :=
  match elemsOf r.vals with
  | none => none
  | some sent =>
    if r.drawn.elems.length == e.drawE &&
        (r.drawn.poss.isEmpty && e.poss == 0) &&
        (r.drawn.trits.isEmpty && e.trits == 0) &&
        e.rows == 0 &&
        e.name != Model.RoundName.batSigma.name &&
        Params.kindOf e.name == some (kindAsked e.name) then
      some { name := some e.name, nz := e.drawNZ, rows := e.rows, sent := sent,
             drawn := r.drawn.elems.map E.ofTriple }
    else none

/-- The stretch's rounds with the stretch's entries, one for one. -/
def tapeS : List Fmt.RoundView → List Fmt.Entry → Option Tape
  | [], [] => some []
  | r :: rs, e :: es =>
    match roundS r e, tapeS rs es with
    | some x, some t => some (x :: t)
    | _, _ => none
  | _, _ => none

/-- **The lookup's messages.** calls, pub, lid: the routine's three public arguments. es: the plan's
entries of the stretch. -/
def lookRun (calls : Array Call) (pub : Array Nat) (lid : Nat) (es : List Fmt.Entry) (F : Fork)
    (rs : List Fmt.RoundView) : Option (Model.Forest.Heard × Fork) :=
  match tapeS rs es with
  | none => none
  | some t =>
    match lkPad calls pub lid F t with
    | some (g, G, []) => some (g, G)
    | _ => none

/-- The same as a step of a chain's decision. fork: the ledger in the state. put: the state with
what was heard and the ledger behind. The number that it returns is that of the opened columns that
it has taken: none. -/
def lookStep {S : Type} (fork : S → Fork) (put : S → Model.Forest.Heard → Fork → S)
    (calls : Array Call) (pub : Array Nat) (lid : Nat) (es : List Fmt.Entry) :
    S → List Fmt.RoundView → List (Nat × Nat × List UInt64) → Option (S × Nat) :=
  fun s rs _ => (lookRun calls pub lid es (fork s) rs).map fun x => (put s x.1 x.2, 0)

end VerifiableInference.Desc.First.Look
