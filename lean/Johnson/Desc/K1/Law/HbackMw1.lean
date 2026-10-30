-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/HbackMw1.lean: K01_law: ONE SMALL TOOL FOR LAYING hback_point (Johnson/Desc/K1/Law/ExchangeAtReads.lean) INTO THE TOP: an item «formsT l j n» that the table's row at the reads' place closes has its tied public item «formsInT l j n» open in front of the place
(readsRow_full [kernel]): so the top's own binder hRd pays hback_point's first pointwise condition. AND tieOut_full [kernel; with a twin that bites]: that row OPENS «tie l»: so the top hands hArm's payer the tie at this w (without it hArm binds «∀ w» bare and cannot be met).
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.ExchangeAtReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (Item Pub flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull rowQ)
open VerifiableInference.Desc.K13.Law (openAt)

theorem formsInT_of_ins (l : ℕ) (hl : l < 25) (j : ℕ) (n : String)
    (h : Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins) :
    Pub.formsInT l j n ∈ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)) := by
  have hrow : readsRowB l (noL l false) = true :=
    List.all_eq_true.1 readsRow_full l (List.mem_range.2 hl)
  unfold readsRowB at hrow
  rw [Bool.and_eq_true] at hrow
  have t := List.all_eq_true.1 hrow.2 _ h
  simp only [Bool.and_eq_true] at t
  exact List.contains_iff_mem.1 t.1.2

/-- The test: the table's row at each reads' place OPENS the item «tie l». -/
def tieOutB : Bool :=
  (List.range 25).all fun l => (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).outs.contains (Item.tie l)

set_option maxRecDepth 1000000 in
theorem tieOutB_true : tieOutB = true := by decide +kernel

/-- **The row at the reads' place of link l opens «tie l».** -/
theorem tieOut_full (l : ℕ) (hl : l < 25) : Item.tie l ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).outs :=
  List.contains_iff_mem.1 (List.all_eq_true.1 tieOutB_true l (List.mem_range.2 hl))

set_option maxRecDepth 1000000 in
/-- **The test can fail**: at segment 3's digits' place; and another segment's tie at segment 3's reads' place. -/
theorem tieOut_fails :
    (rowQ linksFull (flatPlacesOf linksFull true) (noL 3 true)).outs.contains (Item.tie 3) = false ∧
      (rowQ linksFull (flatPlacesOf linksFull true) (noL 3 false)).outs.contains (Item.tie 4) = false := by
  decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.tieOut_full
#print axioms VerifiableInference.Desc.K1.formsInT_of_ins
