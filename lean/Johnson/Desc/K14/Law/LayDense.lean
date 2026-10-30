-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LayDense.lean: how a structured vector on a vector's entries reads on the table
that holds the vector, for vectors that may have a written-out factor.

Johnson/Desc/K14/Law/Lay.lean shows it for vectors without a written-out factor. Here the
written-out variables are followed through the exchange of the index's low and high bits.
Main names: testBit_swap, denseIndex_map, onTable_entryG, laid_sumG, dense_of_ok.

What is not claimed. The written-out variables must be variables of the vector (below its number of
variables): a premise, which a well-formed vector (Tensor.ok) meets. Every equation is between
readings, not between the program's words.

-/
import Johnson.Desc.K14.Law.TensorsDense
import Johnson.Desc.K14.Law.Means

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes
open OnBytes.Model (Reading)

variable {K : Type} [Field K] (ρ : Reading K)

/-- Two bits that are equal as truth values are equal as numbers. -/
theorem bit_eq_of_testBit (x y i k : Nat) (h : x.testBit i = y.testBit k) :
    x / 2 ^ i % 2 = y / 2 ^ k % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h
  have a := Nat.mod_two_eq_zero_or_one (x / 2 ^ i)
  have b := Nat.mod_two_eq_zero_or_one (y / 2 ^ k)
  by_cases e : x / 2 ^ i % 2 = 1 <;> by_cases f : y / 2 ^ k % 2 = 1 <;> simp [e, f] at h <;> omega

/-- Where a bit of an index goes when its low pb bits are moved above the others. -/
theorem testBit_swap (pb rb j d : Nat) (hj : j < 2 ^ rb * 2 ^ pb) (hd : d < rb + pb) :
    (swap (2 ^ pb) (2 ^ rb) j).testBit (if pb ≤ d then d - pb else d + rb) = j.testBit d := by
  have h1 : j / 2 ^ pb < 2 ^ rb := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hj)
  have e : swap (2 ^ pb) (2 ^ rb) j = 2 ^ rb * (j % 2 ^ pb) + j / 2 ^ pb := by
    unfold swap; ring
  rw [e, Nat.testBit_two_pow_mul_add _ h1]
  by_cases h : pb ≤ d
  · rw [if_pos h, if_pos (by omega), Nat.testBit_div_two_pow, Nat.sub_add_cancel h]
  · rw [if_neg h, if_neg (by omega), Nat.add_sub_cancel, Nat.testBit_mod_two_pow]
    simp [Nat.lt_of_not_le h]

/-- The index within the slice, where each written-out variable is followed to its new place. -/
theorem denseIndex_map (f : Nat → Nat) (J j : Nat) : ∀ (ds : List Nat) (i : Nat),
    (∀ d ∈ ds, J / 2 ^ f d % 2 = j / 2 ^ d % 2) →
    denseIndex (ds.map f) i J = denseIndex ds i j
  | [], _, _ => rfl
  | d :: ds, i, h => by
    rw [List.map_cons, denseIndex, denseIndex, h d List.mem_cons_self,
      denseIndex_map f J j ds (i + 1) fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **A structured vector on a vector's entries, read on the table**, with or without a written-out
factor: at the index of entry j it has the vector's entry j, and 0 from 2 ^ (its variables) on. -/
theorem onTable_entryG (lay : VectorLay) (v : Tensor) (hdv : ∀ d ∈ v.denseVars, d < v.vars)
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
    have hidx : denseIndex
        ((v.denseVars.map fun d => if v.vars ≤ d then d + (lay.bits - v.vars) else d).map fun d =>
          if lay.placeBits ≤ d then d - lay.placeBits else d + lay.rowBits) 0
        (swap (2 ^ lay.placeBits) (2 ^ lay.rowBits) j) =
        denseIndex (v.denseVars.map fun d => if v.vars ≤ d then d + (lay.bits - v.vars) else d) 0
          j := by
      refine denseIndex_map _ _ _ _ _ fun d hd => ?_
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.1 hd
      have h0 := hdv d0 hd0
      have e0 : (if v.vars ≤ d0 then d0 + (lay.bits - v.vars) else d0) = d0 :=
        if_neg (by omega)
      rw [e0]
      refine bit_eq_of_testBit _ _ _ _ (testBit_swap _ _ _ _ (by rwa [e] at hj) ?_)
      unfold VectorLay.bits at hv
      omega
    rw [index_eq lay h, Tensor.entry_val, Tensor.entry_val]
    simp only [VectorLay.onTable, h, if_true, Tensor.rotate, Tensor.denseVal, Tensor.insertChoice,
      List.isEmpty_map]
    have := pairsVal_rotate ρ _ lay.placeBits lay.rowBits j hl (by rwa [e] at hj)
    simp only [Tensor.insertChoice] at this
    rw [this, hidx]

/-- Vectors with n variables, laid on a table and applied to it: the sum over the vector's first
2 ^ n entries. -/
theorem laid_sumG (lay : VectorLay) (L : List Tensor) (n : Nat)
    (hL : ∀ t ∈ L, (∀ d ∈ t.denseVars, d < t.vars) ∧ t.vars = n) (hn : n ≤ lay.bits)
    (w : Nat → K) :
    ∑ i ∈ Finset.range (2 ^ lay.bits),
        (L.map fun t => ρ.val ((lay.onTable t).entry i)).sum * w i =
      ∑ j ∈ Finset.range (2 ^ n), (L.map fun t => ρ.val (t.entry j)).sum * w (lay.index j) := by
  rw [sum_index lay]
  have hg : ∀ j ∈ Finset.range (2 ^ lay.bits),
      (L.map fun t => ρ.val ((lay.onTable t).entry (lay.index j))).sum =
        if j < 2 ^ n then (L.map fun t => ρ.val (t.entry j)).sum else 0 := by
    intro j hj
    rw [← sum_map_ite]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    have h0 := onTable_entryG ρ lay t (hL t ht).1 (by rw [(hL t ht).2]; exact hn) j
      (Finset.mem_range.1 hj)
    rwa [(hL t ht).2] at h0
  have hsub : Finset.range (2 ^ n) ⊆ Finset.range (2 ^ lay.bits) :=
    Finset.range_mono (Nat.pow_le_pow_right (by decide) hn)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [hg j (hsub hj), if_pos (Finset.mem_range.1 hj)]
  · intro j hj hnj
    rw [hg j hj, if_neg (fun h => hnj (Finset.mem_range.2 h)), zero_mul]

/-- What a well-formed vector gives: its written-out variables are variables of it, each named once.
-/
theorem dense_of_ok (v : Tensor) (h : v.ok = true) :
    (∀ d ∈ v.denseVars, d < v.vars) ∧ distinctNats v.denseVars = true := by
  simp only [Tensor.ok, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun d hd => ?_, h.2⟩
  have h1 := h.1.2 d hd
  cases hp : v.pairs[d]? with
  | none => rw [hp] at h1; cases h1
  | some p => exact (List.getElem?_eq_some_iff.1 hp).1

end Desc.K14.Law
