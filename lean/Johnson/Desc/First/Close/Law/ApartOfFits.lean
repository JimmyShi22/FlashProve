-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/ApartOfFits.lean (kind K10): "NO TWO MESSAGES HAVE ONE PLACE IN THE
BOOK" (`PlacesApart`, FillRow.lean, beside this file: a premise of rowSays_of_taken,
k10_rows_at_table, k10_rows_at_cube and a field of RowAsks) FOLLOWS OUTRIGHT FROM THE TEST "THE BOOK
FITS" (`K12.Door.atFirstFits`, Johnson/Desc/K12/Door/DoorBools.lean), WHICH IS A FIELD OF THE FACTS
ON
REACHED STATES (`FoldFacts.bookFits`, Johnson/Desc/First/FoldFacts.lean). Two theorems.

Why it holds. The test says of every message number i that has a place q in the book: the tree
number q.1 is there, and its list of parts holds, at q.2, just i. So a place names its message.

What is said.
  `apart_of_fits`: atFirstFits s = true gives PlacesApart s. NO OTHER PREMISE.
  `apart_of_facts`: so at every reached state without a mark, under FoldFacts.

Limits. FoldFacts is a premise: whoever holds it pays. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.FillRow
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart PlacesApart FoldFacts FoldData)

/-- **The book fits: so a place names its message.** -/
theorem apart_of_fits (s : S) (h : VerifiableInference.Desc.K12.Door.atFirstFits s = true) :
    PlacesApart s := by
  have key : ∀ (o : Nat) (x : Nat × Nat), s.book.place[o]? = some x →
      ∃ t, s.book.trees[x.1]? = some t ∧ t.parts[x.2]? = some o := by
    intro o x ho
    have hlt : o < s.book.place.size := (Array.getElem?_eq_some_iff.1 ho).1
    have h0 := List.all_eq_true.1 h o (List.mem_range.2 hlt)
    rw [ho] at h0
    have h1 : (match s.book.trees[x.1]? with
      | some t => decide (t.parts[x.2]? = some o)
      | none => false) = true := h0
    cases ht : s.book.trees[x.1]? with
    | none =>
      rw [ht] at h1
      exact absurd (show false = true from h1) Bool.false_ne_true
    | some t =>
      rw [ht] at h1
      exact ⟨t, rfl, of_decide_eq_true h1⟩
  intro o o' x ho ho'
  obtain ⟨t, ht, hp⟩ := key o x ho
  obtain ⟨t', ht', hp'⟩ := key o' x ho'
  obtain rfl : t = t' := Option.some.inj (ht.symm.trans ht')
  exact Option.some.inj (hp.symm.trans hp')

/-- **So at every reached state without a mark.** -/
theorem apart_of_facts {X P : Type} {Rch : Nat → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) (k : Nat) (a : X) (hr : Rch k a)
    (hu : (at_ a).2.failed = none) : PlacesApart (at_ a).2 :=
  apart_of_fits _ (FF.bookFits k a hr hu)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.apart_of_fits
#print axioms VerifiableInference.Desc.First.Close.apart_of_facts
