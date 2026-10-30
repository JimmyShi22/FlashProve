-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Ahead.lean: THE PUBLIC TEST ON A RUN's FORMS WHERE A FORM NAMES AN ARRAY
THAT THE OPEN SEGMENT HAS
NOT YET SENT. Definitions with code and small lemmas. No Mathlib.

Why. The table of joints opens the item on the smallness test's single equations right behind that
test's own block: one block IN FRONT of the segment's third sending, which brings the digits' array:
every one of these equations names its cells. The test `formsIn`
(Johnson/Desc/First/Batch/FormsIn.lean) finds an array through the RECORD (its message is sent; the
book has its place): there it says no, on an honest walk too. But the item may read the whole
group's seats BY THE PLAN, and the witness is one for all borders.
  `aheadOf sent a b`: the array of the name b is of the open segment's own link, in a message that
  is
    NOT YET SENT: gives the array, THE SEAT THAT THE PLAN GIVES THAT MESSAGE, and its shape by the
    request's shape. sent: the plan's lists of seats of this segment, moment by moment. THE RULE FOR
    THE SEAT: the message's place among its link's messages of the same moment, in the plan's list
    for that moment; at the first sending (moment 0): nothing.
  `rowBitsOf`, `placeBitsOf`: the bits that index a table's rows and places, off a message's shape
  and
    the codes; `rowBits_of`, `placeBits_of`: they are the statement's own at a message of that
    shape.
  `aheadIn sent own a b`: ... AND THAT SEAT IS ONE OF own: the seats that may be read.
  `entInA`, `affInA`, `formsInA`: as `entIn`, `affIn`, `formsIn`, "... or a cell, within its rows
  and
    columns, of an array that is ahead".
  `entInA_of_entIn`, `affInA_of_affIn`, `formsInA_of_formsIn`: the new tests are the weaker ones.
  `aheadOf_mem`, `aheadIn_mem`: the seat is one of the plan's; one of own.
  `entInA_none`, `affInA_none`: where nothing is ahead they are the old ones.
Limits: (1) THAT THE RULE FOR THE SEAT GIVES THE PLACE AT WHICH THE BOOK WILL HOLD THE MESSAGE ONCE
IT IS SENT is not shown here: a test for a walk, and a premise of the riding across the sending.
(2) AT MOMENT 0 IT GIVES NOTHING, BY THE MAKE: where the first sending holds kept copies of earlier
links' messages the rule does not fit (by a walk over one small proof: it fits at the first segment
alone). Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.FormsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- What the plan says of an array that is not yet sent. -/
structure Ahead where
  /-- the array, by the layout -/
  A : Params.ReqArray
  /-- the seat (tree, tenant) that the plan gives its message -/
  seat : Nat × Nat
  /-- its message's shape, by the request's shape -/
  shape : OracleShape

/-- The bits that index a row of a table, off the message's shape: what `Statement.rowBits` gives at
an oracle message of that shape (`rowBits_of`). -/
def rowBitsOf (x : OracleShape) (part : OnBytes.Part) : Nat := ceilLog2 (x.rows part)

/-- The bits that index a place in a row of a table, off the message's shape and the codes: what
`Statement.placeBits` gives (`placeBits_of`). -/
def placeBitsOf (codes : Codes) (x : OracleShape) (part : OnBytes.Part) : Nat :=
  if x.rows part == 0 then 0
  else match part with
    | .main => (codes.base.getD x.code default).logEll
    | .mask => (codes.mask.getD x.maskCode default).logEll

/-- They are the statement's own, at a message of that shape. -/
theorem rowBits_of (st : Statement) (o : Nat) (x : OnBytes.Oracle) (part : OnBytes.Part)
    (h : st.oracles[o]? = some x) : st.rowBits o part = rowBitsOf x.shape part := by
  unfold Statement.rowBits rowBitsOf
  rw [h]

theorem placeBits_of (st : Statement) (o : Nat) (x : OnBytes.Oracle) (part : OnBytes.Part)
    (h : st.oracles[o]? = some x) : st.placeBits o part = placeBitsOf st.codes x.shape part := by
  unfold Statement.placeBits placeBitsOf
  rw [h]
  rfl

section
variable (sent : Nat → List (Nat × Nat))

/-- **An array of the open segment's own link whose message is not yet sent.** -/
def aheadOf (a : Part) (b : Nat × String) : Option Ahead :=
  if b.1 == a.L.check.frame.link then
    (reqArray a.L.check.rows.layout b.1 b.2).bind fun A =>
      match a.L.check.frame.whereIs b.1 A.message with
      | some _ => none
      | none =>
        ((a.L.check.frame.shape.link[b.1]?).map (·.messages)).bind fun ms =>
          (ms[A.message]?).bind fun M =>
            if M.moment == 0 then none
            else ((sent M.moment)[((ms.take A.message).filter fun x =>
              x.moment == M.moment).length]?).map fun x => ⟨A, x, M.shape⟩
  else none

/-- The seat is one of the plan's. -/
theorem aheadOf_mem (a : Part) (b : Nat × String) (h : Ahead) (e : aheadOf sent a b = some h) :
    ∃ k, h.seat ∈ sent k := by
  unfold aheadOf at e
  split at e
  · obtain ⟨A, _, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    · exact nomatch e
    · obtain ⟨ms, _, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨M, _, e⟩ := Option.bind_eq_some_iff.1 e
      split at e
      · exact nomatch e
      · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 e
        subst e
        exact ⟨M.moment, List.mem_of_getElem? hx⟩
  · exact nomatch e

variable (own : List (Nat × Nat)) (free : Option Nat) (late : List (Nat × E × E))

/-- **... and the plan's seat is one that may be read.** -/
def aheadIn (a : Part) (b : Nat × String) : Option Ahead :=
  (aheadOf sent a b).filter fun h => own.contains h.seat

theorem aheadIn_mem (a : Part) (b : Nat × String) (h : Ahead) (e : aheadIn sent own a b = some h) :
    h.seat ∈ own := by
  unfold aheadIn at e
  obtain ⟨_, h2⟩ := Option.filter_eq_some_iff.1 e
  simpa using h2

/-- An entry names a cell that is there, or a cell of an array that is ahead. -/
def entInA (a : Part) (x : Ent) : Bool :=
  entIn own a x ||
    match (a.L.arrayOf[x.tree]?).bind (aheadIn sent own a) with
    | some h => decide (x.row < h.A.sizeI) && decide (x.idx < h.A.sizeC)
    | none => false

/-- A form names only what is there or ahead. -/
def affInA (a : Part) (f : Aff) : Bool :=
  (f.ents.toList.all fun x => entInA sent own a x) &&
    f.slots.toList.all fun x => slotIn own free late a x.1

theorem entInA_of_entIn (a : Part) (x : Ent) (h : entIn own a x = true) :
    entInA sent own a x = true := by
  unfold entInA
  rw [h]
  rfl

theorem affInA_of_affIn (a : Part) (f : Aff) (h : affIn own free late a f = true) :
    affInA sent own free late a f = true := by
  unfold affIn at h
  unfold affInA
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact Eq.mpr (Bool.and_eq_true _ _)
    ⟨List.all_eq_true.2 fun x hx => entInA_of_entIn sent own a x (List.all_eq_true.1 h1 x hx), h2⟩

/-- Where nothing is ahead the test is the old one. -/
theorem entInA_none (a : Part) (hn : ∀ b, aheadIn sent own a b = none) (x : Ent) :
    entInA sent own a x = entIn own a x := by
  unfold entInA
  cases e : a.L.arrayOf[x.tree]? with
  | none => simp
  | some b => simp [hn b]

theorem affInA_none (a : Part) (hn : ∀ b, aheadIn sent own a b = none) (f : Aff) :
    affInA sent own free late a f = affIn own free late a f := by
  unfold affInA affIn
  simp only [entInA_none sent own a hn]

end

section
variable (Rd : Readers) (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))

/-- FOR THE PROMISE, where a run's forms may name what is ahead. -/
def formsInA (piece : Nat) (run : String) (s : S) : Bool :=
  match segAt? s, Rd.forms piece run s with
  | some a, some R =>
    lateOk R.late a && R.forms.all fun f => affInA sent own (mergeOf s) R.late a f
  | _, _ => false

theorem formsInA_of_formsIn (piece : Nat) (run : String) (s : S)
    (h : formsIn Rd own piece run s = true) : formsInA Rd sent own piece run s = true := by
  unfold formsIn at h
  unfold formsInA
  cases ea : segAt? s with
  | none =>
    rw [ea] at h
    exact nomatch h
  | some a =>
    cases er : Rd.forms piece run s with
    | none =>
      rw [ea, er] at h
      exact nomatch h
    | some R =>
      rw [ea, er] at h
      have h' : (lateOk R.late a &&
          R.forms.all fun f => affIn own (mergeOf s) R.late a f) = true := h
      obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h'
      show (lateOk R.late a && R.forms.all fun f => affInA sent own (mergeOf s) R.late a f) = true
      exact Eq.mpr (Bool.and_eq_true _ _) ⟨h1, List.all_eq_true.2 fun f hf =>
        affInA_of_affIn sent own (mergeOf s) R.late a f (List.all_eq_true.1 h2 f hf)⟩

end

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.rowBits_of
#print axioms VerifiableInference.Desc.K9.placeBits_of
#print axioms VerifiableInference.Desc.K9.aheadOf_mem
#print axioms VerifiableInference.Desc.K9.aheadIn_mem
#print axioms VerifiableInference.Desc.K9.affInA_of_affIn
#print axioms VerifiableInference.Desc.K9.affInA_none
#print axioms VerifiableInference.Desc.K9.formsInA_of_formsIn
