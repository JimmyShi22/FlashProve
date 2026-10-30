-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Sum.lean: a sum over the indices of a group's table whose row is in one member's
block is the sum over the member's own indices.

Main theorems: groupIndex_lt, unshift_lt, block_sum, weight_sum.

What is not claimed. The block is assumed aligned and inside the table (BlockOk).

-/
import OnBytes.Iop.RowLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

/-- An index of a member's table of 2^a rows and 2^l places goes to an index of the group's table of
2^k rows and 2^l places. -/
theorem groupIndex_lt (idx a first k l : Nat) (h : BlockOk a first k) (hi : idx < 2 ^ (a + l)) :
    groupIndex idx a first k < 2 ^ (k + l) := by
  unfold groupIndex
  have hq : idx / 2 ^ a < 2 ^ l := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    exact hi
  have hm := Nat.mod_lt idx (Nat.two_pow_pos a)
  have hin := h.inside
  have h1 : (idx / 2 ^ a + 1) * 2 ^ k ≤ 2 ^ l * 2 ^ k := Nat.mul_le_mul_right _ hq
  rw [Nat.add_mul, Nat.one_mul] at h1
  rw [Nat.pow_add, Nat.mul_comm (2 ^ k)]
  omega

/-- An index of the group's table goes back to an index of the member's table. -/
theorem unshift_lt (J a first k l : Nat) (h : BlockOk a first k) (hJ : J < 2 ^ (k + l)) :
    unshift a (k - a) J < 2 ^ (a + l) := by
  unfold unshift
  rw [Nat.add_sub_cancel' h.le]
  have hq : J / 2 ^ k < 2 ^ l := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    exact hJ
  have hm := Nat.mod_lt J (Nat.two_pow_pos a)
  have h1 : 2 ^ a * (J / 2 ^ k + 1) ≤ 2 ^ a * 2 ^ l := Nat.mul_le_mul_left _ hq
  rw [Nat.mul_add, Nat.mul_one] at h1
  rw [Nat.pow_add]
  omega

/-- The sum over the indices whose row is in the block is the sum over the member's indices. -/
theorem block_sum {M : Type} [AddCommMonoid M] (a first k l : Nat) (h : BlockOk a first k)
    (f : Nat → M) :
    (∑ J ∈ (Finset.range (2 ^ (k + l))).filter
        (fun J => first ≤ J % 2 ^ k ∧ J % 2 ^ k < first + 2 ^ a), f J) =
      ∑ idx ∈ Finset.range (2 ^ (a + l)), f (groupIndex idx a first k) := by
  symm
  apply Finset.sum_nbij' (fun idx => groupIndex idx a first k) (fun J => unshift a (k - a) J)
  · intro idx hidx
    rw [Finset.mem_range] at hidx
    rw [Finset.mem_filter, Finset.mem_range, groupIndex_row _ _ _ _ h]
    have hm := Nat.mod_lt idx (Nat.two_pow_pos a)
    exact ⟨groupIndex_lt idx a first k l h hidx, by omega, by omega⟩
  · intro J hJ
    rw [Finset.mem_filter, Finset.mem_range] at hJ
    rw [Finset.mem_range]
    exact unshift_lt J a first k l h hJ.1
  · intro idx _
    exact unshift_groupIndex idx a first k h
  · intro J hJ
    rw [Finset.mem_filter] at hJ
    show groupIndex (unshift a (k - a) J) a first k = J
    rw [groupIndex_eq_shiftIn _ _ _ _ h]
    exact (shiftIn_eq_iff _ _ _ _ _).2 ⟨(inBlock_iff J a first k h).2 hJ.2, rfl⟩
  · intro idx _
    rfl

/-- The same with a weight that is 1 in the block and 0 outside. -/
theorem weight_sum {K : Type} [CommRing K] (a first k l : Nat) (h : BlockOk a first k)
    (f : Nat → K) :
    (∑ J ∈ Finset.range (2 ^ (k + l)),
      (if first ≤ J % 2 ^ k ∧ J % 2 ^ k < first + 2 ^ a then (1 : K) else 0) * f J) =
      ∑ idx ∈ Finset.range (2 ^ (a + l)), f (groupIndex idx a first k) := by
  rw [← block_sum a first k l h f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro J _
  split <;> simp

end OnBytes.Means
