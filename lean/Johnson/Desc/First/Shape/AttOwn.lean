-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/AttOwn.lean: THE SHAPE OF WHAT AN ATTENTION LINK HOLDS BESIDE ITS CONTEXT,
ITS LEDGER, THE SMALLNESS TEST's STATE, WHAT THE LOOKUP RETURNED AND ITS TABLES: what is left of
the other fields of First.AttOwn (Johnson/Desc/First/State.lean) when every field element is left
out. Definitions, and four small laws. Nothing is evaluated.

What it is for. Johnson/Desc/First/Shape/Chain.lean lays the shapes of the state's parts together.
The link's own rounds (kind K5, Johnson/Desc/First/Att/K5AttentionKind.lean, at the seat seatSO, Att/SeatO.lean)
lay the field heard5; the quiet step behind the sending of the reads (Att/ReadsO.lean) and the
kind's runs of claims (Att/RunsK.lean) read it.

THE FIELDS' TYPES. No field holds a field element.
  `SumSh`      of Part.MaskedSum.Heard (Johnson/Desc/Part/MaskedSum4.lean): start : AffSh
               (Parts.lean): the shape of the form that the sum is claimed to equal · first sEnd :
               Nat (slots) · degrees : List Nat: each variable's number of coefficients, the further
               variable's last (of Var.point z d the point z is an element: out) · r : Nat: the
               number of challenges. target, eps and claim are elements: out.
  `Heard5Sh`   of Att.P.Heard (Att/K5Heard.lean): remainders : List Nat (slots) · scores : List (Nat
               × SumSh) · five bits two values maxima : Nat (slots), each under its own name · gam
               point om om' om'' : Nat (the sizes of five arrays of elements) · division below on
               atIndex key cells : SumSh.
  `AttOwnSh`   of AttOwn: planes scores : Bool (that the Option is laid) · heard5 : Option Heard5Sh.
NOT SEEN HERE, since the chain's shape sees them by components of their own: L, F, tl, g (look),
lookHeard, and of t its list of tables. OUT, WHOLE: d and x: blanks from the link's entry on
(State.lean, S.enterAtt), which no text at the seat seatSO reads or lays (Att/SeatO.lean's head); so
with the content of planes and scores; and what t holds beside its list of tables (the quiet step
behind the sending of the reads lays t whole). The makers lay no default: an Option stays an Option.
  `sumSh`, `heard5Sh`, `attOwnSh`, `attOf`: the last reads the link's fields off a place of the
  chain.
  `attOf_isSome`, `attOwnSh_enter`, `attOwnSh_blind`, `attOwnSh_heard5`: where it is there; at the
  link's entry; what it does not see; what the hearing turns.

Limits. Definitions. No update is here: what the hearing lays as a function of the plan and the next
slot is typed elsewhere. A number can still be made of a value: which numbers of these structures
are the plan's or counts is argued elsewhere. A guard that reads the content of planes, scores, d or
x, or of t more than its list of tables, cannot be written on this shape.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Shape.Parts
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First

/-- What the hearing of a masked sumcheck hands back. -/
structure SumSh where
  start : AffSh
  first : Nat
  degrees : List Nat
  r : Nat
  sEnd : Nat

def sumSh (h : Part.MaskedSum.Heard) : SumSh :=
  { start := affSh h.start, first := h.first, degrees := h.vars.map (·.d), r := h.r.length
    sEnd := h.sEnd }

/-- What an attention link's own rounds hand on. -/
structure Heard5Sh where
  remainders : List Nat
  scores : List (Nat × SumSh)
  five : Nat
  bits : Nat
  two : Nat
  division : SumSh
  gam : Nat
  values : Nat
  below : SumSh
  on : SumSh
  point : Nat
  maxima : Nat
  om : Nat
  atIndex : SumSh
  om' : Nat
  key : SumSh
  om'' : Nat
  cells : SumSh

def heard5Sh (h : Att.P.Heard) : Heard5Sh :=
  { remainders := h.remainders.toList, scores := h.scores.toList.map fun o => (o.1, sumSh o.2)
    five := h.five, bits := h.bits, two := h.two, division := sumSh h.division, gam := h.gam.size
    values := h.values, below := sumSh h.below, on := sumSh h.on, point := h.point.size
    maxima := h.maxima, om := h.om.size, atIndex := sumSh h.atIndex, om' := h.om'.size
    key := sumSh h.key, om'' := h.om''.size, cells := sumSh h.cells }

/-- **An attention link's own fields.** -/
structure AttOwnSh where
  /-- the list of plane claims is laid -/
  planes : Bool
  /-- the list of the softmax-table units is laid -/
  scores : Bool
  heard5 : Option Heard5Sh

def attOwnSh (a : AttOwn) : AttOwnSh :=
  { planes := a.planes.isSome, scores := a.scores.isSome, heard5 := a.heard5.map heard5Sh }

/-- An attention link's own fields, where the chain stands in such a link. -/
def attOf : Here → Option AttOwnSh
  | .att a => some (attOwnSh a)
  | _ => none

/-- It is there just where the chain stands in an attention link. -/
theorem attOf_isSome (x : Here) : (attOf x).isSome = true ↔ ∃ a, x = .att a := by
  cases x <;> simp [attOf]

/-- At a link's entry (S.enterAtt, Johnson/Desc/First/State.lean) nothing is laid. -/
theorem attOwnSh_enter (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    attOwnSh { L := L, F := F, tl := tl, d := default, x := default } =
      { planes := false, scores := false, heard5 := none } := by
  rfl

/-- The ledger, the link's context, the smallness test's state, what the lookup returned and the
tables are not seen. -/
theorem attOwnSh_blind (a : AttOwn) (L : LinkCtx) (F : Fork) (tl : HTailF2)
    (g lookHeard : Option Forest.Heard) (t : Option Attention.Tables) (d : Attention.Divide)
    (x : Attention.Attain) :
    attOwnSh
        { a with
          L := L, F := F, tl := tl, g := g, lookHeard := lookHeard, t := t, d := d, x := x } =
      attOwnSh a := by
  rfl

/-- What the hearing lays (S.hear5) turns one field. -/
theorem attOwnSh_heard5 (a : AttOwn) (h : Att.P.Heard) :
    attOwnSh { a with heard5 := some h } = { attOwnSh a with heard5 := some (heard5Sh h) } := by
  rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.attOf_isSome
#print axioms VerifiableInference.Desc.First.Shape.attOwnSh_enter
#print axioms VerifiableInference.Desc.First.Shape.attOwnSh_blind
#print axioms VerifiableInference.Desc.First.Shape.attOwnSh_heard5
