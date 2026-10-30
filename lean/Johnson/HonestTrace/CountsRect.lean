-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsRect.lean

If 5 ≤ lm ≤ kT + 5, the address FoNums.cellRC h lm (t, c, j) of a bit with t < 2^kT, c < NC and j <
32 lies inside the planes' matrix of 2^lm rows and NC 2^(kT + 5 - lm) columns.

Notation: as in Johnson/HonestTrace/Counts.lean; NC and kT are fields of h : Forest.Shape.

Main theorem:
* "cellRC_in": if 5 ≤ lm ≤ kT + 5, t < 2^kT, c < NC and j < 32, then FoNums.cellRC h lm (t, c, j)
  has its row below 2^lm and its column below NC 2^(kT + 5 - lm).

Use. The conditions LaidB, LaidBA and LaidBH (Johnson/HonestTrace/CountsLayers.lean,
CountsAttention.lean, CountsHead.lean) speak of the rows and columns below these two numbers alone;
bitsG_plane, bitsA_plane and bitsH_plane use this theorem for the places FoNums.cellRC at which
G.bitsG, A.bitsA and H.bitsH read, where 5 ≤ lm ≤ kT + 5.

Limits. Numbers alone: no key, table or cell occurs.

-/
import Johnson.HonestTrace.Counts

set_option autoImplicit false

namespace OnBytes.HonestTrace

open OnBytes.Model

/-- If 5 ≤ lm ≤ kT + 5, t < 2^kT, c < NC and j < 32, then the row of FoNums.cellRC h lm (t, c, j) is
below 2^lm and its column is below NC 2^(kT + 5 - lm). -/
theorem cellRC_in (h : Forest.Shape) {lm : ℕ} (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) {t c j : ℕ}
    (ht : t < 2 ^ h.kT) (hc : c < h.NC) (hj : j < 32) :
    (FoNums.cellRC h lm (t, c, j)).1 < 2 ^ lm ∧
      (FoNums.cellRC h lm (t, c, j)).2 < h.NC * 2 ^ (h.kT + 5 - lm) := by
  constructor
  · show t % 2 ^ (lm - 5) * 32 + j < 2 ^ lm
    have e : 2 ^ lm = 2 ^ (lm - 5) * 32 := by
      rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_add]
      congr 1
      omega
    have h1 : t % 2 ^ (lm - 5) < 2 ^ (lm - 5) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : (t % 2 ^ (lm - 5) + 1) * 32 ≤ 2 ^ (lm - 5) * 32 := Nat.mul_le_mul_right _ h1
    rw [e]
    omega
  · show c * 2 ^ (h.kT + 5 - lm) + t / 2 ^ (lm - 5) < h.NC * 2 ^ (h.kT + 5 - lm)
    have h1 : t / 2 ^ (lm - 5) < 2 ^ (h.kT + 5 - lm) := by
      apply Nat.div_lt_of_lt_mul
      rw [← pow_add, show lm - 5 + (h.kT + 5 - lm) = h.kT by omega]
      exact ht
    have h2 : (c + 1) * 2 ^ (h.kT + 5 - lm) ≤ h.NC * 2 ^ (h.kT + 5 - lm) :=
      Nat.mul_le_mul_right _ hc
    rw [Nat.succ_mul] at h2
    omega

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.cellRC_in
