-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedLate.lean: what the world of the shipped Lean verifier's forms holds at an
entry of an array that is committed late.

The entries are of two kinds, J₁ ⊕ J₂: those that are fixed before the chain's first round, and
those of a message that is sent later (the reads of a sub-proof). Cb/Sub/Late.lean says when the
late entries u agree with public forms a on the early entries m: u i = (a i).val m for all i.

Main theorems. portWorld_entry_cell: where a virtual row has the weight 1 on one row of its array
and 0 on the others, its entry in portWorld is the committed cell. portWorld_entry_late: for a cell
among the late entries that is u i. portWorld_entry_agree: where u agrees with a, it is the value
of the form a i on the early entries. So a statement on portWorld's entries of the late array, at
entries that agree, is a statement on the early entries alone.

What this file does not claim. That the late entries agree is another block's claim. That a virtual
row of the late array has such weights is a fact on the verifier's plan, asked here as a premise.


-/
import OnBytes.Tie.Pv.Led.LedPort
import OnBytes.Tie.Pv.Led.LedLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open TWhole

variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- A virtual row with the weight 1 on row r0 alone: its entry is the committed cell. -/
theorem portWorld_entry_cell {J : Type} [Fintype J] (Y : Lay J) (F : Model.Fork) (m : J → K)
    (t r r0 idx : Nat) (hw : rowWeight ρ F.trees t r = fun k => if k = r0 then 1 else 0) :
    (portWorld ρ Y F m).entry t r idx = Y.cellAt m t r0 idx := by
  rw [portWorld_entry, hw, Lay.entryAt_unit]

variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] (Y : Lay (J₁ ⊕ J₂))

/-- The same for a cell among the late entries. -/
theorem portWorld_entry_late (F : Model.Fork) (m : J₁ → K) (u : J₂ → K) (t r r0 idx : Nat)
    (i : J₂) (hw : rowWeight ρ F.trees t r = fun k => if k = r0 then 1 else 0)
    (ha : Y.addr (.inr i) = .cell t r0 idx) :
    (portWorld ρ Y F (Sum.elim m u)).entry t r idx = u i := by
  rw [portWorld_entry_cell ρ Y F _ t r r0 idx hw, Y.cellAt_addr _ t r0 idx (.inr i) ha,
    Sum.elim_inr]

/-- Where the late entries agree with the forms a, the entry is the form's value on the early
entries. -/
theorem portWorld_entry_agree (F : Model.Fork) (a : J₂ → Aff K J₁) (m : J₁ → K) (u : J₂ → K)
    (hu : ∀ i, u i = (a i).val m) (t r r0 idx : Nat) (i : J₂)
    (hw : rowWeight ρ F.trees t r = fun k => if k = r0 then 1 else 0)
    (ha : Y.addr (.inr i) = .cell t r0 idx) :
    (portWorld ρ Y F (Sum.elim m u)).entry t r idx = (a i).val m := by
  rw [portWorld_entry_late ρ Y F m u t r r0 idx i hw ha, hu i]

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.portWorld_entry_cell
#print axioms OnBytes.Road.Rows.portWorld_entry_late
#print axioms OnBytes.Road.Rows.portWorld_entry_agree
