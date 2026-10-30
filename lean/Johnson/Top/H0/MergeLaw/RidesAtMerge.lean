-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RidesAtMerge.lean: THE FIRST CUT: WHICH ITEMS THE MERGE's FIFTH
TIE SPEAKS OF: at the written list of places at the full size, at the merge's number 346: what is
open in front of the sub-protocol and is neither closed nor read by its row: SIXTEEN ITEMS, BY NAME.
A closed fact, by Lean's kernel (decide +kernel; no native code).

  ridesAtMerge     the sixteen, written out
  ridesB_full      the test with code: every member of the computed list of what is open at border
                   346 (openL, Johnson/Desc/Sound/SpineList.lean) that is no member of the row's ins
                   is one of the sixteen; and each of the sixteen is such a member
  rides_mem        **openAfter … 346 i → ¬ insQ … 346 i → i ∈ ridesAtMerge**
  t5_of_each       so the fifth tie follows from one sentence for each of the sixteen

Limits. At linksFull and flatPlacesOf linksFull true alone. It says of no item that it rides.
Nothing on soundness.

-/
import Johnson.Desc.Sound.SpineList
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.Sound (openAfter insQ outsQ openL insL outsL openIsList linksFull relQ
  meansQ)
open VerifiableInference.Desc.First (S Item RowClass Numbers Meaning start flatPlacesOf)

/-- **What is open at the merge's number and is not the row's**: sixteen items. -/
def ridesAtMerge : List Item :=
  [.pile, .row 24 .carried, .row 24 (.sample 0), .row 24 .position, .row 24 (.sample 1),
    .forms 24 3 "objects", .forms 24 3 "planes", .forms 24 4 "join", .forms 24 4 "own",
    .forms 24 6 "small", .row 24 (.sample 2), .forms 24 8 "objects", .worth 24 8 "planes",
    .worth 24 8 "keys", .pin 24 2, .pin 24 1]

/-- The computed list: what is open at border 346, without the row's ins. -/
def ridesL : List Item :=
  (openL (insL linksFull (flatPlacesOf linksFull true))
    (outsL linksFull (flatPlacesOf linksFull true)) (start linksFull) 346).filter fun i =>
      decide (i ∉ insL linksFull (flatPlacesOf linksFull true) 346)

/-- The test with code: the two lists have the same members. -/
def ridesB : Bool :=
  (ridesL.all fun i => decide (i ∈ ridesAtMerge)) && ridesAtMerge.all fun i => decide (i ∈ ridesL)

set_option maxRecDepth 1000000 in
theorem ridesB_full : ridesB = true := by decide +kernel

/-- **The items of which the fifth tie speaks.** -/
theorem rides_mem (i : Item)
    (h : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) 346 i)
    (hn : ¬ insQ linksFull (flatPlacesOf linksFull true) 346 i) : i ∈ ridesAtMerge := by
  have h1 : i ∈ openL (insL linksFull (flatPlacesOf linksFull true))
      (outsL linksFull (flatPlacesOf linksFull true)) (start linksFull) 346 :=
    (openIsList Item _ _ _ 346 i).1 h
  have h2 : i ∈ ridesL := List.mem_filter.2 ⟨h1, decide_eq_true hn⟩
  have h3 := ridesB_full
  unfold ridesB at h3
  exact of_decide_eq_true (List.all_eq_true.1 ((Bool.and_eq_true _ _).mp h3).1 i h2)

/-- **So the fifth tie follows from one sentence for each of the sixteen**: where the relation holds
at the border behind, and each of the sixteen goes back from b to a. -/
theorem t5_of_each {A P W : Type} {Fr : VerifiableInference.Desc.Sound.Frame} (N : Numbers)
    (Mg : Meaning P W) (get : A → P × S) (a b : A × Fr.E.Str) (w : W)
    (hrel : relQ N Mg linksFull (flatPlacesOf linksFull true) get (346 + 1) b w)
    (hE : ∀ i ∈ ridesAtMerge, meansQ N Mg get i b w → meansQ N Mg get i a w) (i : Item)
    (h : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) 346 i)
    (hn : ¬ insQ linksFull (flatPlacesOf linksFull true) 346 i) : meansQ N Mg get i a w :=
  hE i (rides_mem i h hn) (hrel i (Or.inl ⟨h, hn⟩))

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.t5_of_each
#print axioms VerifiableInference.Desc.First.MergeLaw.ridesB_full
#print axioms VerifiableInference.Desc.First.MergeLaw.rides_mem
