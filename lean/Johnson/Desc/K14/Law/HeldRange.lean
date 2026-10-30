-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/HeldRange.lean: Spec.held (Johnson/Desc/K14/Law/HeldRangeSpec.lean), proved: a
third member of HeldTie: the cells are the matrix of the top statements' configuration, kept under
any test of range. A theorem.
Limits. R is a letter. That cellsAt is the configuration's own cellsOf is not said in Lean here.
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.HeldRangeSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- **Where a matrix is kept, it is the decoded table's.** -/
theorem heldTie_range : Spec.held := by
  intro p err₂ eM rank cut R hcut hell U c h y hy col hcol
  unfold heldIf at h
  split at h
  · obtain rfl := Option.some.inj h
    have hc : col < 2 ^ (p.S.kLo + p.S.fold.index.v) := hcol
    have hm : col % 2 ^ p.S.kLo < 2 ^ p.S.kLo := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hk : col % 2 ^ p.S.kLo + 2 ^ p.S.kLo * y < p.S.matrixRows * 2 ^ p.S.kLo := by
      have h1 : 2 ^ p.S.kLo * (y + 1) ≤ 2 ^ p.S.kLo * p.S.matrixRows :=
        Nat.mul_le_mul_left _ hy
      rw [Nat.mul_comm p.S.matrixRows]
      rw [Nat.mul_add, Nat.mul_one] at h1
      omega
    unfold matAt
    rw [dif_pos ⟨hy, hc⟩]
    unfold cellsAt
    rw [dif_pos ⟨Nat.lt_of_lt_of_le hk hell, Nat.lt_of_lt_of_le hk hcut⟩]
    show _ = tabU p err₂ eM rank U (col / 2 ^ p.S.kLo) (col % 2 ^ p.S.kLo + 2 ^ p.S.kLo * y)
    unfold tabU
    rw [dif_pos (Nat.lt_of_lt_of_le hk hell)]
  · cases h

end Desc.K14.Law
