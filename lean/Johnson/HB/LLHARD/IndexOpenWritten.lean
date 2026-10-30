--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/IndexOpenWritten.lean: two things that the law on the reader through the chain
state's own book asks of the plan and of the table at the places of the kind K1 (`reader_four`,
Johnson/Desc/K13/Law/ReaderFour.lean): the test "the plan's places name trees that are there" (the
field `below` of `PlanK13`, Johnson/Desc/K13/Law/MgK13.lean), and that the public item "the index
masks' message is there" is asked at these places.

1 The field `below`. Its text is, to the letter, the conclusion of `below_of_plan`
(Johnson/Desc/K13/Law/PlanTestsM3.lean). At the written layout `LFull`
(Johnson/HB/LLHARD/LaidWritten.lean) and at numbers that are laid off what the sub-protocols tell,
it follows from one premise on what they tell (`CountsAre`, Johnson/HB/LLHARD/ToldCounts.lean) by
three lemmas that lie: `planBelow_written` (ToldCounts.lean), `planBelow_withTold`, `below_of_plan`.
It holds at every place. No evaluation is made for it here.
  `planBelow_of_counts`: `PlanBelow LFull (N.withTold pl told)`. `below_of_counts`: the field's
    text.

2 The item. The table ties the public item `indexThere` to the open item `pinI`, the pin of the
index masks' message (`pubOfItems`, Johnson/Desc/First/Borders.lean): it is asked at a border just
as long as that pin is open there.
  `pinOpenB j`: a test: at every border from number j on the pin is open. ONE walk of the open sets.
  `pinOpen_written`: it accepts from border 3 on. `pinOpen_rejects`: the negative test: from border
    2 on it rejects: the pin is opened by the sub-protocol number 2, the first segment's opening.
    `open_count`: 359 open sets are walked.
  `pin_at`: so the pin is open at every border k with 3 ≤ k ≤ 358. `indexThere_at`: and the item is
    among the tied items there.
  `later_numbers`: each of the fifty later sendings' places (`laterFull`,
    Johnson/HB/LLHARD/PlanAtQFull.lean) stands in the list of places at a number from 3 to 357.
    `indexThere_later`: so the item is asked in front of each of the fifty.
By evaluations in Lean's kernel (`decide +kernel`): `pinOpen_written`, `pinOpen_rejects`,
`open_count`, `later_numbers`.

Limits. Closed facts on the table at the full size's list of segments, and one law under a premise.
That other public items are asked at the fifty is not said here. Nothing on soundness.
-/
import Johnson.HB.LLHARD.ToldCounts
import Johnson.HB.LLHARD.PlanAtQFull
import Johnson.Desc.K13.Law.AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S Item Pub Numbers flatPlacesOf openSets start pubOfItems)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K12.Door (seatsCarriedB placesBelowB)

/-! ## 1 The plan's places name trees that are there -/

theorem planBelow_of_counts (N : Numbers) {told : List (List Oracle)} (h : CountsAre told) :
    PlanBelow LFull (N.withTold (flatPlacesOf linksFull true) told) :=
  planBelow_withTold N (flatPlacesOf linksFull true) told (by
    rw [places_fit.1]
    exact planBelow_written h)

/-- **The field `below` of `PlanK13`, to the letter**, at the written layout and at numbers laid off
what the sub-protocols tell. -/
theorem below_of_counts {Pp : Type} (N : Numbers) {told : List (List Oracle)}
    (h : CountsAre told) :
    ∀ (x : Pp × S) p, First.bookAt (N.withTold (flatPlacesOf linksFull true) told) p x.2 = true →
      seatsCarriedB LFull x.2.book = true →
      placesBelowB LFull x.2.book.place.size x.2.book.trees.size = true :=
  below_of_plan (planBelow_of_counts N h)

/-! ## 2 The index masks' pin is open -/

/-- At every border from number j on the index masks' pin is open. -/
def pinOpenB (j : ℕ) : Bool :=
  ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull)).drop j).all fun O =>
    decide (Item.pinI ∈ O)

set_option maxRecDepth 1000000 in
theorem pinOpen_written : pinOpenB 3 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: at border 2 it is not open yet. -/
theorem pinOpen_rejects : pinOpenB 2 = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem open_count :
    (openSets linksFull (flatPlacesOf linksFull true) (start linksFull)).length = 359 := by
  decide +kernel

/-- **The pin is open at every border from 3 to 358.** -/
theorem pin_at {k : ℕ} (h0 : 3 ≤ k) (hk : k ≤ 358) :
    Item.pinI ∈ openAt linksFull (flatPlacesOf linksFull true) k := by
  have hlt : k < (openSets linksFull (flatPlacesOf linksFull true) (start linksFull)).length := by
    rw [open_count]
    omega
  have hO := List.getElem?_eq_getElem hlt
  have hd : ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull)).drop 3)[k - 3]? =
      some (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k] := by
    rw [List.getElem?_drop, show 3 + (k - 3) = k by omega]
    exact hO
  have a := of_decide_eq_true (List.all_eq_true.1 pinOpen_written _ (List.mem_of_getElem? hd))
  unfold openAt
  rw [hO]
  exact a

/-- **So the public item is among the tied items there.** -/
theorem indexThere_at {k : ℕ} (h0 : 3 ≤ k) (hk : k ≤ 358) :
    Pub.indexThere ∈ pubOfItems (openAt linksFull (flatPlacesOf linksFull true) k) :=
  List.mem_flatMap.2 ⟨Item.pinI, pin_at h0 hk, List.Mem.tail _ (List.Mem.head _)⟩

set_option maxRecDepth 1000000 in
/-- Each of the fifty places stands in the list of places, at a number from 3 to 357. -/
theorem later_numbers : (laterFull.all fun x =>
    decide (3 ≤ (flatPlacesOf linksFull true).idxOf ⟨1, some x.1, x.2.1, .K1⟩ ∧
      (flatPlacesOf linksFull true).idxOf ⟨1, some x.1, x.2.1, .K1⟩ ≤ 357)) = true := by
  decide +kernel

/-- **The item is asked in front of each of the fifty later sendings.** -/
theorem indexThere_later {x : ℕ × ℕ × ℕ × ℕ × ℕ} (hx : x ∈ laterFull) :
    Pub.indexThere ∈ pubOfItems (openAt linksFull (flatPlacesOf linksFull true)
      ((flatPlacesOf linksFull true).idxOf ⟨1, some x.1, x.2.1, .K1⟩)) := by
  have a := of_decide_eq_true (List.all_eq_true.1 later_numbers x hx)
  exact indexThere_at a.1 (by omega)

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.planBelow_of_counts
#print axioms VerifiableInference.Desc.K13.Law.below_of_counts
#print axioms VerifiableInference.Desc.K13.Law.pinOpen_written
#print axioms VerifiableInference.Desc.K13.Law.pinOpen_rejects
#print axioms VerifiableInference.Desc.K13.Law.open_count
#print axioms VerifiableInference.Desc.K13.Law.pin_at
#print axioms VerifiableInference.Desc.K13.Law.indexThere_at
#print axioms VerifiableInference.Desc.K13.Law.later_numbers
#print axioms VerifiableInference.Desc.K13.Law.indexThere_later
