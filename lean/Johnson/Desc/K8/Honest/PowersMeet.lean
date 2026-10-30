-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PowersMeet.lean: IN A FINITE FIELD: AT HOW MANY x TWO OF THE POWERS (x ^ N) ^
i, i < m, ARE EQUAL. Statements and proofs. Algebra alone: no block, no prover, no data of the
protocol. Lemmas; none of the library's goals.

  **`root_one_few`**   0 < n: at most n elements have x ^ n = 1
  **`powers_meet_few`**   0 < N: at most 1 + the sum over k < m of N * k elements x have (x ^ N) ^ i
      = (x ^ N) ^ j at some i < j < m
  `powers_sum`   that sum is at most N * m * m
The argument: x is 0, or x ^ (N * (j - i)) = 1 at a difference between 0 and m; a union over the
differences.
By: K9L.count_terms (Johnson/Desc/First/Batch/Law/Count.lean) · Prob.cnt_exists_mem_le, cnt_le_add,
cnt_le_one (Prob/Count.lean).
Limits. A union bound, no exact count. What it is meant for, the test that the row weights of a
matrix's array of symbols differ (tieWeightsHeld, OnBytes/Model/Tail.lean), is named by no lemma
here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.Law.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc

/-- **The roots of one.** -/
theorem root_one_few (K : Type) [Field K] [Fintype K] (n : ℕ) (hn : 0 < n) :
    Prob.cnt (fun x : K => x ^ n = 1) ≤ n := by
  have h := K9L.count_terms K [(n, (1 : K)), (0, (-1 : K))] n
    ⟨by simp [hn.ne'], by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact Nat.le_refl _
      · exact Nat.zero_le _⟩
    ⟨(n, 1), by simp, one_ne_zero⟩
  refine le_trans (Prob.cnt_mono fun x hx => ?_) h
  show K9L.termsSum [(n, (1 : K)), (0, (-1 : K))] x = 0
  unfold K9L.termsSum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, mul_one, one_mul,
    add_zero]
  rw [hx]
  ring

/-- **Two of the powers are equal.** -/
theorem powers_meet_few (K : Type) [Field K] [Fintype K] (N m : ℕ) (hN : 0 < N) :
    Prob.cnt (fun x : K => ∃ i j, i < j ∧ j < m ∧ (x ^ N) ^ i = (x ^ N) ^ j) ≤
      1 + ∑ k ∈ Finset.range m, N * k := by
  have hsplit : ∀ x : K, (∃ i j, i < j ∧ j < m ∧ (x ^ N) ^ i = (x ^ N) ^ j) →
      x = 0 ∨ ∃ k ∈ Finset.range m, 0 < k ∧ x ^ (N * k) = 1 := by
    rintro x ⟨i, j, hij, hj, he⟩
    by_cases hx : x = 0
    · exact Or.inl hx
    · refine Or.inr ⟨j - i, Finset.mem_range.2 (by omega), by omega, ?_⟩
      have hy : (x ^ N) ^ i ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hx)
      have e1 : (x ^ N) ^ j = (x ^ N) ^ i * (x ^ N) ^ (j - i) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e1] at he
      have e2 : (x ^ N) ^ i * (x ^ N) ^ (j - i) = (x ^ N) ^ i * 1 := by rw [mul_one, ← he]
      rw [pow_mul]
      exact mul_left_cancel₀ hy e2
  refine le_trans (Prob.cnt_le_add hsplit) (Nat.add_le_add
    (Prob.cnt_le_one fun _ _ ha hb => ha.trans hb.symm) ?_)
  refine le_trans (Prob.cnt_exists_mem_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  by_cases hk : 0 < k
  · exact le_trans (Prob.cnt_mono fun x hx => hx.2) (root_one_few K _ (Nat.mul_pos hN hk))
  · rw [Prob.cnt_false fun x hx => hk hx.1]
    exact Nat.zero_le _

/-- A plain bound on the sum. -/
theorem powers_sum (N m : ℕ) : ∑ k ∈ Finset.range m, N * k ≤ N * m * m := by
  calc ∑ k ∈ Finset.range m, N * k ≤ ∑ _k ∈ Finset.range m, N * m :=
        Finset.sum_le_sum fun k hk => Nat.mul_le_mul_left _ (Finset.mem_range.1 hk).le
    _ = N * m * m := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.root_one_few
#print axioms VerifiableInference.Desc.First.K8.Honest.powers_meet_few
#print axioms VerifiableInference.Desc.First.K8.Honest.powers_sum
