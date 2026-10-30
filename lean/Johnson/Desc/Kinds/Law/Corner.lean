-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Corner.lean: THE EQUALITY WEIGHT, READ IN THE FIELD (L1 of the road).
`wt`: the product with one factor a coordinate. `rd_eq`: HeadParts.lean's `eq z i` is read as it.
`rd_eq_bits`: at the point whose coordinates are the bits of t it is 1 at i = t and 0 elsewhere.
`sum_wt`: the weights of all indices add up to 1. `sum_blocks`: a sum over blocks of S entries.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)

/-- One factor for each coordinate, that of the highest bit first: x if the bit of i is 1, else
1 - x. -/
def wt : List K → Nat → K
  | [], _ => 1
  | x :: xs, i => (if i.testBit xs.length then x else 1 - x) * wt xs i

theorem rd_eq_fold (i : Nat) : ∀ (l : List E) (s : E),
    rd ((l.foldl (fun (s : E × Nat) x =>
      (if i.testBit (s.2 - 1) then s.1 * x else s.1 - s.1 * x, s.2 - 1)) (s, l.length)).1)
      = rd s * wt (l.map rd) i
  | [], s => by simp [wt]
  | x :: xs, s => by
    simp only [List.foldl_cons, List.length_cons, Nat.add_sub_cancel, List.map_cons, wt,
      List.length_map]
    rw [rd_eq_fold i xs]
    split
    · rw [rd_mul]; ring
    · rw [rd_sub, rd_mul]; ring

theorem rd_eq (z : Point) (i : Nat) :
    rd (eq z i) = if i < 2 ^ z.size then wt (z.toList.map rd) i else 0 := by
  unfold eq
  split
  · have h := rd_eq_fold i z.toList 1
    rw [Array.length_toList, Array.foldl_toList, rd_one, one_mul] at h
    exact h
  · exact rd_zero

/-- A weight depends on the low bits alone. -/
theorem wt_congr : ∀ (l : List K) (i i' : Nat),
    (∀ j, j < l.length → i.testBit j = i'.testBit j) → wt l i = wt l i'
  | [], _, _, _ => rfl
  | x :: xs, i, i', h => by
    simp only [wt]
    rw [h xs.length (by simp), wt_congr xs i i' fun j hj => h j (by simp; omega)]

/-- The weights of all indices add up to 1. -/
theorem sum_wt : ∀ (l : List K), (Finset.range (2 ^ l.length)).sum (wt l) = 1
  | [] => by simp [wt]
  | x :: xs => by
    have ih := sum_wt xs
    rw [List.length_cons, pow_succ, Nat.mul_two, Finset.sum_range_add]
    have h1 : (Finset.range (2 ^ xs.length)).sum (wt (x :: xs))
        = (1 - x) * (Finset.range (2 ^ xs.length)).sum (wt xs) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [wt]
      rw [Nat.testBit_lt_two_pow (Finset.mem_range.mp hi)]
      simp
    have h2 : (Finset.range (2 ^ xs.length)).sum (fun i => wt (x :: xs) (2 ^ xs.length + i))
        = x * (Finset.range (2 ^ xs.length)).sum (wt xs) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [wt]
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (Finset.mem_range.mp hi),
        wt_congr xs (2 ^ xs.length + i) i fun j hj => Nat.testBit_two_pow_add_gt hj i]
      simp
    rw [h1, h2, ih]; ring

/-! ## A corner -/

/-- The bits of t, read. -/
def bK (n t : Nat) : List K := (List.range n).map fun j => if t.testBit (n - 1 - j) then 1 else 0

theorem bK_length (n t : Nat) : (bK n t).length = n := by simp [bK]

theorem bK_succ (n t : Nat) : bK (n + 1) t = (if t.testBit n then 1 else 0) :: bK n t := by
  unfold bK
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp]
  have : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
  rw [this]

theorem map_rd_bits (n t : Nat) : (bits n t).toList.map rd = bK n t := by
  unfold bits bK
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp]
  split
  · exact rd_one
  · exact rd_zero

theorem wt_bK : ∀ (n t i : Nat),
    wt (bK n t) i = if ∀ j, j < n → i.testBit j = t.testBit j then 1 else 0
  | 0, _, _ => by simp [bK, wt]
  | n + 1, t, i => by
    rw [bK_succ]
    simp only [wt, bK_length]
    rw [wt_bK n t i]
    by_cases hn : i.testBit n = t.testBit n
    · by_cases hl : ∀ j, j < n → i.testBit j = t.testBit j
      · have : ∀ j, j < n + 1 → i.testBit j = t.testBit j := by
          intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
          · exact hl j h
          · subst h; exact hn
        rw [if_pos hl, if_pos this]
        cases hi : i.testBit n <;> rw [hi] at hn <;> simp [← hn]
      · have : ¬ ∀ j, j < n + 1 → i.testBit j = t.testBit j :=
          fun h => hl fun j hj => h j (Nat.lt_succ_of_lt hj)
        rw [if_neg hl, if_neg this, mul_zero]
    · have : ¬ ∀ j, j < n + 1 → i.testBit j = t.testBit j :=
        fun h => hn (h n (Nat.lt_succ_self n))
      rw [if_neg this]
      cases hi : i.testBit n <;> cases ht : t.testBit n <;> simp_all

/-- **At a corner the equality weight is 1 at its own index and 0 elsewhere.** -/
theorem rd_eq_bits {n t : Nat} (ht : t < 2 ^ n) (i : Nat) :
    rd (eq (bits n t) i) = if i = t then 1 else 0 := by
  have hs : (bits n t).size = n := by simp [bits]
  rw [rd_eq, hs, map_rd_bits, wt_bK]
  by_cases hi : i < 2 ^ n
  · rw [if_pos hi]
    by_cases he : i = t
    · subst he; simp
    · rw [if_neg he, if_neg]
      intro h
      apply he
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < n
      · exact h j hj
      · have hle : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hi hle),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le ht hle)]
  · rw [if_neg hi, if_neg]
    intro he; subst he; exact hi ht

/-- The weights at a point of n coordinates add up to 1. -/
theorem sum_rd_eq (z : Point) : (Finset.range (2 ^ z.size)).sum (fun i => rd (eq z i)) = 1 := by
  have h := sum_wt (z.toList.map rd)
  rw [List.length_map, Array.length_toList] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [rd_eq, if_pos (Finset.mem_range.mp hi)]

/-! ## Blocks -/

/-- A sum over n blocks of S entries is the sum over the n S entries. -/
theorem sum_blocks {M : Type} [AddCommMonoid M] (S : Nat) (g : Nat → M) : ∀ n : Nat,
    (Finset.range n).sum (fun i => (Finset.range S).sum fun j => g (S * i + j))
      = (Finset.range (n * S)).sum g
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_blocks S g n, Nat.succ_mul, Finset.sum_range_add,
      Nat.mul_comm S n]

end VerifiableInference.Desc.Kinds.Head.Law
