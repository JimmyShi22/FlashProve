-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Tables.lean: THE TWO TABLES OF THE HEAD's ONE SUMCHECK (for Lemma 2b). An index of
lt + lPd bits is a position (the high bits) and a feature (the low bits); a feature from d on is
padding and holds 0. `mle_cut`: such a table's extension at a point in two parts is the double sum
over positions and features below d. `sigma_eq`: summed at zt ++ halves lPd the product of the two
tables is 2^-lPd times HeadLaw.lean's `trueSum`.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Decode

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE)
open Norm (lt ls d lPd T S2)
open OnBytes.Desc.First.P1 (mle tot)

theorem le_two_pow_clog2 (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · simpa using ‹n ≤ 1›
  · have := Nat.lt_log2_self (n := n - 1)
    omega

theorem sum_ite_lt {M : Type} [AddCommMonoid M] {a b : Nat} (h : a ≤ b) (f : Nat → M) :
    (Finset.range b).sum (fun x => if x < a then f x else 0) = (Finset.range a).sum f := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Under coordinates h with 1 - h = h every index has the weight h^m. -/
theorem wt_replicate (h : K) (hh : 1 - h = h) : ∀ (m i : Nat), wt (List.replicate m h) i = h ^ m
  | 0, _ => by simp [wt]
  | m + 1, i => by
    simp only [List.replicate_succ, wt, hh, ite_self]
    rw [wt_replicate h hh m i, pow_succ]
    ring

/-- A table over positions and features: feature k of position t at the index 2^m t + k; 0 from
feature n on. -/
def cut (m n : Nat) (f : Nat → Nat → K) (bs : List Bool) : K :=
  if idxOf bs % 2 ^ m < n then f (idxOf bs / 2 ^ m) (idxOf bs % 2 ^ m) else 0

theorem cut_mul (m n : Nat) (f g : Nat → Nat → K) (bs : List Bool) :
    cut m n f bs * cut m n g bs = cut m n (fun t k => f t k * g t k) bs := by
  unfold cut
  split <;> simp

/-- **The extension of such a table at a point in two parts.** -/
theorem mle_cut (a b : List K) (n : Nat) (hn : n ≤ 2 ^ b.length) (f : Nat → Nat → K) :
    mle (a ++ b).length (cut b.length n f) (a ++ b)
      = (Finset.range (2 ^ a.length)).sum fun t => (Finset.range n).sum fun k =>
          wt a t * wt b k * f t k := by
  refine (mle_idx (a ++ b) (fun i => if i % 2 ^ b.length < n then
      f (i / 2 ^ b.length) (i % 2 ^ b.length) else 0)).trans ?_
  rw [sum_two_parts]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← sum_ite_lt hn]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hpos : 0 < 2 ^ b.length := by positivity
  have h1 : (2 ^ b.length * t + k) / 2 ^ b.length = t := by
    rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hk', Nat.add_zero]
  have h2 : (2 ^ b.length * t + k) % 2 ^ b.length = k := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk']
  simp only [h1, h2]
  split <;> simp

/-- The weights of a point, as HeadParts.lean's `eq` gives them. -/
theorem wt_toList (z : Point) {i : Nat} (hi : i < 2 ^ z.size) :
    wt (z.toList.map rd) i = rd (eq z i) := by
  rw [rd_eq, if_pos hi]

/-! ## The head's two tables -/

variable [Sizes] [Policy] [Request] [Token]

theorem half_K : (1 : K) - (2 : K)⁻¹ = (2 : K)⁻¹ := by
  have h2 : (2 : K) ≠ 0 := by simpa using two_pow_ne_zero 1
  field_simp
  norm_num

theorem rd_half : rd half = (2 : K)⁻¹ := by
  unfold half
  rw [rd_inv, rd_ofNat]
  norm_num

theorem map_rd_halves (m : Nat) : (halves m).toList.map rd = List.replicate m (2 : K)⁻¹ := by
  unfold halves
  simp [rd_half]

/-- act, as a table's function of position and feature. -/
def fA (c : Cells) (t k : Nat) : K := ((act c t k : Int) : K)

section In
variable [FinalNorm.In] [In]

/-- UH, as a table's function of position and feature. -/
def fU (c : Cells) (t k : Nat) : K := rd (UH c k t)

theorem rd_trueSum' (c : Cells) : rd (trueSum c) = (Finset.range T).sum fun t =>
    (Finset.range d).sum fun k => rd (eq FinalNorm.zt t) * fA c t k * fU c t k := by
  unfold trueSum
  rw [rd_sumTo]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [rd_sumTo]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rd_mul, rd_mul, rd_ofInt]
  rfl

/-- **The sum of the product of the two tables at zt ++ halves lPd is 2^-lPd times the true sum.** -/
theorem sigma_eq (c : Cells) (hzt : (FinalNorm.zt).size = lt) :
    mle ((FinalNorm.zt).toList.map rd ++ List.replicate lPd (2 : K)⁻¹).length
        (fun bs => cut lPd d (fA c) bs * cut lPd d (fU c) bs)
        ((FinalNorm.zt).toList.map rd ++ List.replicate lPd (2 : K)⁻¹)
      = ((2 : K) ^ lPd)⁻¹ * rd (trueSum c) := by
  have hl : (List.replicate lPd (2 : K)⁻¹).length = lPd := List.length_replicate
  have hd : d ≤ 2 ^ (List.replicate lPd (2 : K)⁻¹).length := by
    rw [hl]; exact le_two_pow_clog2 d
  have h0 : (fun bs => cut lPd d (fA c) bs * cut lPd d (fU c) bs)
      = cut (List.replicate lPd (2 : K)⁻¹).length d (fun t k => fA c t k * fU c t k) := by
    funext bs
    rw [hl, cut_mul]
  rw [h0, mle_cut _ _ d hd, rd_trueSum', Finset.mul_sum, List.length_map, Array.length_toList, hzt]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have ht' : t < 2 ^ (FinalNorm.zt).size := by rw [hzt]; exact Finset.mem_range.mp ht
  rw [wt_toList _ ht', wt_replicate _ half_K, inv_pow]
  ring

end In

end VerifiableInference.Desc.Kinds.Head.Law
