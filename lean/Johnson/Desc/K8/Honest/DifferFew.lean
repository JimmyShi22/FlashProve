-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/DifferFew.lean: IN A FINITE FIELD: AT HOW MANY x AN EVENT HAPPENS THAT, AT
ONE OF n NUMBERS mu, GIVES TWO EQUAL POWERS (x ^ N) ^ i, i < m mu. One statement and its proof.
Algebra alone: no block, no prover, no data of the protocol. A lemma; none of the library's goals.

  **`differ_few`**   0 < N; bad x mu, at mu < n, gives i < j < m mu with (x ^ N) ^ i = (x ^ N) ^ j:
      then at most the sum over mu < n of 1 + the sum over k < m mu of N * k elements x have bad x
      mu at some mu < n
What it is meant for: `differ_no_powers` (Johnson/Desc/K8/Honest/CoefClosed.lean) at the matrices of
a smallness test.
By: `powers_meet_few` (Johnson/Desc/K8/Honest/PowersMeet.lean) · Prob.cnt_exists_mem_le, cnt_mono
(Prob/Count.lean).
Limits. A union bound, no exact count.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.PowersMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc

/-- **The count over the numbers.** -/
theorem differ_few (K : Type) [Field K] [Fintype K] (n N : ℕ) (m : ℕ → ℕ) (hN : 0 < N)
    (bad : K → ℕ → Prop)
    (hb : ∀ x mu, mu < n → bad x mu → ∃ i j, i < j ∧ j < m mu ∧ (x ^ N) ^ i = (x ^ N) ^ j) :
    Prob.cnt (fun x : K => ∃ mu, mu < n ∧ bad x mu) ≤
      ∑ mu ∈ Finset.range n, (1 + ∑ k ∈ Finset.range (m mu), N * k) := by
  refine le_trans (Prob.cnt_mono fun x hx => ?_)
    (le_trans (Prob.cnt_exists_mem_le (Finset.range n)
      fun mu (x : K) => ∃ i j, i < j ∧ j < m mu ∧ (x ^ N) ^ i = (x ^ N) ^ j)
      (Finset.sum_le_sum fun mu _ => powers_meet_few K N (m mu) hN))
  obtain ⟨mu, hmu, h⟩ := hx
  exact ⟨mu, Finset.mem_range.2 hmu, hb x mu hmu h⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.differ_few
