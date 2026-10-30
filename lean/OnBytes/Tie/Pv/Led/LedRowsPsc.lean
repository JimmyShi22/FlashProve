-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedRowsPsc.lean: which virtual rows the claim of a masked sumcheck names, and
which the three claims on the planes of the smallness test's lookup.

Main names.
  rowsIn_addSlots: adding slots to a form adds no entry of a virtual row.
  rowsIn_rowForm: the claim that a sumcheck leaves (Psc.rowForm, OnBytes/Model/Psc.lean) names the
    virtual rows that its start form and the kept form name, and no other.
  rowsIn_bitsL: the three claims on the planes (bitsL, LedWalkTail.lean) name the rows 0, 1 and 2 of
    the array BZ and what the start form of the leaves' sumcheck names.

RowsIn: LedRowsOf.lean.

What this file does not claim. What the start form of a given sumcheck is.


-/
import OnBytes.Tie.Pv.Led.LedRowsOf
import OnBytes.Tie.Pv.Led.LedWalkTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open OnBytes.Model

variable {Q : Nat → Nat → Prop}

theorem rowsIn_addSlots {a : Aff} (first : Nat) (form : Array E) (ha : RowsIn Q a) :
    RowsIn Q (addSlots a first form) := by
  unfold addSlots
  rw [← Array.foldl_toList]
  have key : ∀ (l : List E) (s : Nat × Aff), RowsIn Q s.2 → RowsIn Q (l.foldl addSlot s).2 := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons x l ih =>
      rintro ⟨j, u⟩ h
      exact ih _ (rowsIn_addMul x h (rowsIn_slot j))
  exact key _ _ ha

/-- The claim that a sumcheck leaves. -/
theorem rowsIn_rowForm (p : Psc) (S0 : E) {kept : Aff} (hs : RowsIn Q p.start)
    (hk : RowsIn Q kept) : RowsIn Q (p.rowForm S0 kept) := by
  unfold Psc.rowForm
  exact rowsIn_addMul _ (rowsIn_addMul _ (rowsIn_addSlots _ _ (rowsIn_ofConst _))
    (rowsIn_sub (rowsIn_ofConst _) hs)) hk

/-- The three claims on the planes. -/
theorem rowsIn_bitsL (tl : HTailF2) (g : Forest.Heard) (hs : RowsIn Q g.leaves.start)
    (hq : ∀ e, e < 3 → Q tl.ix.BZ e) : ∀ f ∈ bitsL tl g, RowsIn Q f := by
  intro f hf
  simp only [bitsL, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · refine rowsIn_claimForm (rowsIn_rowForm _ _ hs rowsIn_empty) fun r hr => ?_
    obtain rfl : r = _ := by simpa using hr
    exact hq 0 (by omega)
  · refine rowsIn_claimForm (rowsIn_slot _) fun r hr => ?_
    obtain rfl : r = _ := by simpa using hr
    exact hq 1 (by omega)
  · refine rowsIn_claimForm (rowsIn_ofConst _) fun r hr => ?_
    obtain rfl : r = _ := by simpa using hr
    exact hq 2 (by omega)

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.rowsIn_rowForm
#print axioms OnBytes.Road.Rows.rowsIn_bitsL
