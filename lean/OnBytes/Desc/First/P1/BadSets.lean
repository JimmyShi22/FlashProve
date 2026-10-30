-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/BadSets.lean: the sets of bad drawn elements of the two kinds of rounds in
which nothing is summed, as algebra over a field K: no text of a verifier, no bytes, no tape. In a
batching the verifier draws one element x and uses its powers 1, x, x^2 and so on to make one claim
of n claims. In a point it draws g elements, at which a multilinear extension is read. Definitions,
statements and proofs.

  `batch_bad`: the values c 0, .., c (n - 1) are fixed first. Then there is a set of at most n - 1
    elements such that for every x outside it: if the sum of x^i * c i is 0, every c i is 0.
  `batch_bad_eq`: the same for two rows of values whose batched sums are equal.
  `point_count`, `point_bad` (K finite): the vector d is fixed first. Then there is a set of at most
    g * |K|^(g - 1) points such that for every point outside it: if the extension of d is 0 there,
    every entry of d below 2^g is 0. The set is empty if d is 0 below 2^g. The count is
    `Blocks.cnt_ext_zero_le`; nothing is counted anew here.

What is not shown. No statement here joins a set of bad elements to a run: that the values c (or d)
were fixed before x (or the point) was drawn is the caller's to show. Nothing is said of
probabilities: sets are counted. `Alg.count_powers_le` (Alg/Poly.lean) counts the same roots as
`batch_bad` for a finite domain; `batch_bad` names the set, and K need not be finite.
-/
import Blocks.Ext
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open Polynomial

variable {K : Type} [Field K]

/-! ### One element's powers batch n claims -/

/-- The polynomial with the coefficients c 0, .., c (n - 1). -/
def batchPoly (c : ℕ → K) (n : ℕ) : K[X] := ∑ i ∈ Finset.range n, C (c i) * X ^ i

theorem batchPoly_eval (c : ℕ → K) (n : ℕ) (x : K) :
    (batchPoly c n).eval x = ∑ i ∈ Finset.range n, x ^ i * c i := by
  unfold batchPoly
  rw [eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

theorem batchPoly_coeff (c : ℕ → K) (n i : ℕ) (h : i < n) : (batchPoly c n).coeff i = c i := by
  unfold batchPoly
  rw [finset_sum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro j _ hj
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hj)]
  · intro hi
    exact absurd (Finset.mem_range.mpr h) hi

theorem batchPoly_natDegree_le (c : ℕ → K) (n : ℕ) : (batchPoly c n).natDegree ≤ n - 1 := by
  unfold batchPoly
  refine natDegree_sum_le_of_forall_le _ _ (n := n - 1) fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  exact le_trans (natDegree_C_mul_X_pow_le _ _) (by omega)

/-- **A batching.** The values c and their number n stand first; then the set of bad elements, of at
most n - 1 members (none for n = 0 and n = 1); then x. -/
theorem batch_bad (c : ℕ → K) (n : ℕ) :
    ∃ bad : Finset K, bad.card ≤ n - 1 ∧
      ∀ x, x ∉ bad → ∑ i ∈ Finset.range n, x ^ i * c i = 0 → ∀ i < n, c i = 0 := by
  classical
  refine ⟨(batchPoly c n).roots.toFinset, ?_, ?_⟩
  · calc (batchPoly c n).roots.toFinset.card ≤ Multiset.card (batchPoly c n).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (batchPoly c n).natDegree := card_roots' _
      _ ≤ n - 1 := batchPoly_natDegree_le c n
  · intro x hx hs i hi
    by_contra hne
    have hP : batchPoly c n ≠ 0 := fun h0 =>
      hne (by rw [← batchPoly_coeff c n i hi, h0, coeff_zero])
    apply hx
    rw [Multiset.mem_toFinset, mem_roots hP]
    show (batchPoly c n).eval x = 0
    rw [batchPoly_eval, hs]

/-- A batching of two rows of values: if the batched sums are equal at an x that is not bad, the
rows are equal. -/
theorem batch_bad_eq (a b : ℕ → K) (n : ℕ) :
    ∃ bad : Finset K, bad.card ≤ n - 1 ∧
      ∀ x, x ∉ bad →
        ∑ i ∈ Finset.range n, x ^ i * a i = ∑ i ∈ Finset.range n, x ^ i * b i →
        ∀ i < n, a i = b i := by
  obtain ⟨bad, hc, hb⟩ := batch_bad (fun i => a i - b i) n
  refine ⟨bad, hc, fun x hx hs i hi => sub_eq_zero.mp (hb x hx ?_ i hi)⟩
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hs, sub_self]

/-! ### A point at which an extension is read -/

/-- A set of points at each of which the extension of a vector that is not 0 is 0 has at most
g * |K|^(g - 1) members. This is the count `Blocks.cnt_ext_zero_le`, said of a set. -/
theorem point_count [Fintype K] (g : ℕ) (d : ℕ → K) (hd : ∃ j < 2 ^ g, d j ≠ 0)
    (S : Finset (Fin g → K)) (hS : ∀ p ∈ S, Blocks.ext g d (Blocks.nat p) = 0) :
    S.card ≤ g * Fintype.card K ^ (g - 1) := by
  classical
  have e : Prob.cnt (fun p : Fin g → K => Blocks.ext g d (Blocks.nat p) = 0) =
      (Finset.univ.filter fun p : Fin g → K => Blocks.ext g d (Blocks.nat p) = 0).card := by
    unfold Prob.cnt
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : S ⊆ Finset.univ.filter fun p : Fin g → K => Blocks.ext g d (Blocks.nat p) = 0 :=
    fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ p, hS p hp⟩
  calc S.card
      ≤ (Finset.univ.filter fun p : Fin g → K => Blocks.ext g d (Blocks.nat p) = 0).card :=
        Finset.card_le_card hsub
    _ = Prob.cnt (fun p : Fin g → K => Blocks.ext g d (Blocks.nat p) = 0) := e.symm
    _ ≤ g * Fintype.card K ^ (g - 1) := Blocks.cnt_ext_zero_le g d hd

/-- **A point.** The vector d stands first; then the set of bad points, of at most g * |K|^(g - 1)
members, and empty if d is 0 below 2^g; then the point p. -/
theorem point_bad [Fintype K] (g : ℕ) (d : ℕ → K) :
    ∃ Bad : Finset (Fin g → K), Bad.card ≤ g * Fintype.card K ^ (g - 1) ∧
      ((∀ j < 2 ^ g, d j = 0) → Bad = ∅) ∧
      ∀ p, p ∉ Bad → Blocks.ext g d (Blocks.nat p) = 0 → ∀ j < 2 ^ g, d j = 0 := by
  classical
  by_cases hd : ∃ j < 2 ^ g, d j ≠ 0
  · refine ⟨Finset.univ.filter fun p : Fin g → K => Blocks.ext g d (Blocks.nat p) = 0,
      point_count g d hd _ fun p hp => (Finset.mem_filter.mp hp).2, ?_, ?_⟩
    · intro h0
      obtain ⟨j, hj, hne⟩ := hd
      exact absurd (h0 j hj) hne
    · intro p hp h0
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h0⟩) hp
  · refine ⟨∅, by simp, fun _ => rfl, fun p _ _ j hj => ?_⟩
    by_contra hne
    exact hd ⟨j, hj, hne⟩

end OnBytes.Desc.First.P1
