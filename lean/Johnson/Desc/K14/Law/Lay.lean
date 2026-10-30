-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Lay.lean: how a structured vector on a vector's entries reads on the table that
holds the vector.

Main names: swap_swap, swap_lt, sum_index (a sum over a table's indices is the sum over the vector's
entries), pairsVal_rotate, onTable_entry.

What is not claimed. onTable_entry is for a vector without a written-out factor that has no more
variables than the table. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes
open OnBytes.Model (Reading)
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The number x = a + P b (a below P) becomes b + R a. -/
def swap (P R x : Nat) : Nat := x / P + x % P * R

/-- It stays below P R. -/
theorem swap_lt (P R x : Nat) (h : x < R * P) : swap P R x < P * R := by
  have hP : 0 < P := Nat.pos_of_ne_zero fun e => by simp [e] at h
  have h1 : x / P < R := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)
  have h2 : (x % P + 1) * R ≤ P * R := Nat.mul_le_mul_right R (Nat.mod_lt x hP)
  rw [Nat.succ_mul] at h2
  unfold swap
  omega

/-- Done twice, with P and R exchanged, it gives the number back. -/
theorem swap_swap (P R x : Nat) (h : x < R * P) : swap R P (swap P R x) = x := by
  have hP : 0 < P := Nat.pos_of_ne_zero fun e => by simp [e] at h
  have hR : 0 < R := Nat.pos_of_ne_zero fun e => by simp [e] at h
  have h1 : x / P < R := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)
  unfold swap
  rw [Nat.add_mul_div_right _ _ hR, Nat.add_mul_mod_self_right, Nat.div_eq_of_lt h1,
    Nat.mod_eq_of_lt h1, Nat.zero_add, Nat.mul_comm]
  exact Nat.mod_add_div x P

/-- Where a row holds consecutive entries, the index of an entry is its swap. -/
theorem index_eq (lay : VectorLay) (h : lay.rowsHigh = true) (j : Nat) :
    lay.index j = swap (2 ^ lay.placeBits) (2 ^ lay.rowBits) j := by
  simp [VectorLay.index, h, swap]

/-- A sum over a table's indices is the sum over the entries of the vector that lies in it. -/
theorem sum_index (lay : VectorLay) (f : Nat → K) :
    ∑ i ∈ Finset.range (2 ^ lay.bits), f i =
      ∑ j ∈ Finset.range (2 ^ lay.bits), f (lay.index j) := by
  cases h : lay.rowsHigh with
  | false => simp [VectorLay.index, h]
  | true =>
    have e : 2 ^ lay.bits = 2 ^ lay.rowBits * 2 ^ lay.placeBits := by
      rw [VectorLay.bits, Nat.pow_add]
    have e' : 2 ^ lay.bits = 2 ^ lay.placeBits * 2 ^ lay.rowBits := by rw [e, Nat.mul_comm]
    refine Finset.sum_nbij' (swap (2 ^ lay.rowBits) (2 ^ lay.placeBits))
      (swap (2 ^ lay.placeBits) (2 ^ lay.rowBits)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_range] at ha ⊢
      rw [e]; exact swap_lt _ _ _ (by rwa [e'] at ha)
    · intro a ha
      rw [Finset.mem_range] at ha ⊢
      rw [e']; exact swap_lt _ _ _ (by rwa [e] at ha)
    · intro a ha
      rw [Finset.mem_range] at ha
      exact swap_swap _ _ _ (by rwa [e'] at ha)
    · intro a ha
      rw [Finset.mem_range] at ha
      exact swap_swap _ _ _ (by rwa [e] at ha)
    · intro a ha
      rw [Finset.mem_range] at ha
      rw [index_eq lay h, swap_swap _ _ _ (by rwa [e'] at ha)]

/-- The pairs with the first pb moved behind the others, at the index with its low pb bits moved
above the others. -/
theorem pairsVal_rotate (ps : List (E × E)) (pb rb j : Nat) (hl : ps.length = rb + pb)
    (hj : j < 2 ^ rb * 2 ^ pb) :
    pairsVal ρ (ps.drop pb ++ ps.take pb) (swap (2 ^ pb) (2 ^ rb) j) = pairsVal ρ ps j := by
  have h1 : j / 2 ^ pb < 2 ^ rb := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hj)
  have ld : (ps.drop pb).length = rb := by rw [List.length_drop]; omega
  have lt : (ps.take pb).length = pb := by rw [List.length_take]; omega
  have a := pairsVal_mod ρ (ps.drop pb) (swap (2 ^ pb) (2 ^ rb) j)
  have b := pairsVal_mod ρ (ps.take pb) j
  rw [ld] at a
  rw [lt] at b
  rw [pairsVal_append, ld, ← a]
  unfold swap
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos rb), Nat.div_eq_of_lt h1, Nat.zero_add, b]
  conv_rhs => rw [← List.take_append_drop pb ps]
  rw [pairsVal_append, lt, mul_comm]

/-- A vector with choice variables for 0 above its own, up to n variables: the vector below
2 ^ (its variables), and 0 from there on. -/
theorem entry_widened (v : Tensor) (n J : Nat) (hv : v.vars ≤ n) (hJ : J < 2 ^ n) :
    ρ.val ((v.insertChoice v.vars (n - v.vars) 0).entry J) =
      if J < 2 ^ v.vars then ρ.val (v.entry J) else 0 := by
  rw [Tensor.entry_insertChoice ρ v v.vars (n - v.vars) 0 J (Nat.le_refl _)]
  have e : 2 ^ n = 2 ^ v.vars * 2 ^ (n - v.vars) := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : J / 2 ^ v.vars < 2 ^ (n - v.vars) := Nat.div_lt_of_lt_mul (by rwa [e] at hJ)
  rw [Nat.mod_eq_of_lt h1, Nat.zero_mod]
  by_cases h : J < 2 ^ v.vars
  · have h2 : J / 2 ^ (v.vars + (n - v.vars)) = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [if_pos (Nat.div_eq_of_lt h), if_pos h, one_mul, unshift, Nat.mod_eq_of_lt h, h2]
    simp
  · have h2 : ¬ J / 2 ^ v.vars = 0 := fun e0 => by
      have := Nat.div_add_mod J (2 ^ v.vars)
      have := Nat.mod_lt J (Nat.two_pow_pos v.vars)
      rw [e0] at *
      omega
    rw [if_neg h2, if_neg h, zero_mul]

/-- **A structured vector on a vector's entries, read on the table**: at the index of entry j it has
the vector's entry j, and 0 from 2 ^ (its variables) on. -/
theorem onTable_entry (lay : VectorLay) (v : Tensor) (hd : v.denseVars = [])
    (hv : v.vars ≤ lay.bits) (j : Nat) (hj : j < 2 ^ lay.bits) :
    ρ.val ((lay.onTable v).entry (lay.index j)) =
      if j < 2 ^ v.vars then ρ.val (v.entry j) else 0 := by
  rw [← entry_widened ρ v lay.bits j hv hj]
  cases h : lay.rowsHigh with
  | false => simp [VectorLay.onTable, VectorLay.index, h]
  | true =>
    have e : 2 ^ lay.bits = 2 ^ lay.rowBits * 2 ^ lay.placeBits := by
      rw [VectorLay.bits, Nat.pow_add]
    have hl : (v.insertChoice v.vars (lay.bits - v.vars) 0).pairs.length =
        lay.rowBits + lay.placeBits := by
      have : v.pairs.length = v.vars := rfl
      simp only [Tensor.insertChoice, List.length_append, List.length_take, List.length_drop,
        choicePairs_length]
      unfold VectorLay.bits at hv ⊢
      omega
    rw [index_eq lay h, Tensor.entry_val, Tensor.entry_val]
    simp only [VectorLay.onTable, h, if_true, Tensor.rotate, Tensor.denseVal, Tensor.insertChoice,
      hd, List.map_nil, List.isEmpty_nil]
    have := pairsVal_rotate ρ _ lay.placeBits lay.rowBits j hl (by rwa [e] at hj)
    simp only [Tensor.insertChoice] at this
    rw [this]

end Desc.K14.Law
