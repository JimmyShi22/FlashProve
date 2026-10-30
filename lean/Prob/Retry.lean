-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/Retry.lean: sampling again until a test is passed, at most n + 1 times, and the distribution
of the output.

  `retry ok n`      Sample a uniform element of A; if it passes the test `ok`, output it; otherwise
                    sample again, independently. Sample number n + 1 is output whatever it is.
  `pr_retry_fail`   The output fails the test with probability exactly q^(n + 1), where q (`qFail`)
                    is the probability that one uniform sample fails.
  `map_retry`       A function f of the value that is independent of the test under the uniform
                    distribution has, on the output, the distribution that it has on one uniform
                    sample. (Which sample is output depends on the tests only.)
  `pr_retry_le`     So Pr[f(output) ∈ E, or the output fails the test] is at most Pr[f(x) ∈ E, x
                    uniform] + q^(n + 1).

Independence is stated as: for every value b, Pr[f = b and the test fails] = Pr[f = b] · q.
A is a finite non-empty type.

Use: proof of work ("grinding") in a non-interactive (Fiat-Shamir) proof, where the prover queries a
random oracle at new points until some bits of the answer are 0. No oracle occurs in this file.
-/
import Prob.Count
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal

namespace Prob

variable {A B : Type} [Fintype A] [Nonempty A]

/-- Sample until the test is passed, at most n + 1 times; the last sample is output in any case. -/
def retry (ok : A → Bool) : ℕ → PMF A
  | 0 => unif A
  | n + 1 => (unif A).bind fun x => if ok x then PMF.pure x else retry ok n

/-- the indicator of E, with the decidability instance that `Prob.pr_eq_expect` has, so that this
lemma and `pr_pure` prove `pr_eq_ind1`, `pr_pure_ind1` as they stand -/
private def ind1 {α : Type} (E : Set α) (x : α) : ℝ≥0∞ :=
  @ite ℝ≥0∞ (x ∈ E) (Classical.propDecidable _) 1 0

private theorem ind1_pos {α : Type} {E : Set α} {x : α} (h : x ∈ E) : ind1 E x = 1 := by
  unfold ind1; exact if_pos h
private theorem ind1_neg {α : Type} {E : Set α} {x : α} (h : x ∉ E) : ind1 E x = 0 := by
  unfold ind1; exact if_neg h
private theorem pr_eq_ind1 {α : Type} (p : PMF α) (E : Set α) : pr p E = expect p (ind1 E) :=
  pr_eq_expect p E
private theorem pr_pure_ind1 {α : Type} (a : α) (E : Set α) : pr (PMF.pure a) E = ind1 E a :=
  pr_pure a E

/-- the probability that one uniform sample fails the test -/
def qFail (ok : A → Bool) : ℝ≥0∞ := pr (unif A) {x | ok x = false}

/-- The output fails the test with probability exactly q^(n + 1), q = `qFail ok`. -/
theorem pr_retry_fail (ok : A → Bool) : ∀ n, pr (retry ok n) {x | ok x = false} = qFail ok ^ (n + 1)
  | 0 => by simp [retry, qFail]
  | n + 1 => by
      have h : ∀ x : A, pr (if ok x then PMF.pure x else retry ok n) {x | ok x = false} =
          ind1 {x | ok x = false} x * qFail ok ^ (n + 1) := by
        intro x
        by_cases hx : ok x = true
        · rw [if_pos hx, pr_pure_ind1, ind1_neg (by simp [hx]), zero_mul]
        · have hx' : ok x = false := by simpa using hx
          rw [if_neg hx, pr_retry_fail ok n, ind1_pos (E := {x | ok x = false}) hx', one_mul]
      rw [retry, pr_bind, expect_congr _ h, expect_mul_const, ← pr_eq_ind1,
        pow_succ (qFail ok) (n + 1), mul_comm]
      rfl

/-- If f is independent of the test (`ind`), f of the output has the distribution of f of one
uniform sample. -/
theorem map_retry (ok : A → Bool) (f : A → B)
    (ind : ∀ b, pr (unif A) {x | f x = b ∧ ok x = false} = pr (unif A) {x | f x = b} * qFail ok) :
    ∀ n, (retry ok n).map f = (unif A).map f
  | 0 => rfl
  | n + 1 => by
      ext b
      have ih := map_retry ok f ind n
      have e1 : ((retry ok (n + 1)).map f) b = pr (retry ok (n + 1)) {x | f x = b} := by
        rw [← pr_singleton, pr_map]; rfl
      have e2 : ((unif A).map f) b = pr (unif A) {x | f x = b} := by
        rw [← pr_singleton, pr_map]; rfl
      have e3 : pr (retry ok n) {x | f x = b} = pr (unif A) {x | f x = b} := by
        rw [← e2, ← ih, ← pr_singleton, pr_map]; rfl
      have h : ∀ x : A, pr (if ok x then PMF.pure x else retry ok n) {x | f x = b} =
          ind1 {x | f x = b ∧ ok x = true} x +
            ind1 {x | ok x = false} x * pr (unif A) {x | f x = b} := by
        intro x
        by_cases hx : ok x = true
        · rw [if_pos hx, pr_pure_ind1,
            ind1_neg (E := {x | ok x = false}) (by simp [hx]), zero_mul, add_zero]
          by_cases hb : f x = b
          · rw [ind1_pos (E := {x | f x = b}) hb,
              ind1_pos (E := {x | f x = b ∧ ok x = true}) ⟨hb, hx⟩]
          · rw [ind1_neg (E := {x | f x = b}) hb,
              ind1_neg (E := {x | f x = b ∧ ok x = true}) fun h => hb h.1]
        · have hx' : ok x = false := by simpa using hx
          rw [if_neg hx, e3, ind1_pos (E := {x | ok x = false}) hx', one_mul,
            ind1_neg (E := {x | f x = b ∧ ok x = true}) (fun h => hx h.2), zero_add]
      rw [e1, e2, retry, pr_bind, expect_congr _ h, expect_add, expect_mul_const,
        ← pr_eq_ind1, ← pr_eq_ind1]
      have hs : pr (unif A) {x | f x = b} =
          pr (unif A) {x | f x = b ∧ ok x = true} + pr (unif A) {x | f x = b ∧ ok x = false} := by
        rw [← pr_union_of_disjoint]
        · congr 1
          ext x
          cases hx : ok x <;> simp [hx]
        · rw [Set.disjoint_left]
          rintro x ⟨_, h1⟩ ⟨_, h2⟩
          rw [h1] at h2
          cases h2
      show pr (unif A) {x | f x = b ∧ ok x = true} + qFail ok * pr (unif A) {x | f x = b} = _
      rw [mul_comm, ← ind b, ← hs]

/-- Under `ind`: Pr[f(output) ∈ E, or the output fails the test] ≤ Pr[f(x) ∈ E, x uniform] +
q^(n + 1). -/
theorem pr_retry_le (ok : A → Bool) (f : A → B)
    (ind : ∀ b, pr (unif A) {x | f x = b ∧ ok x = false} = pr (unif A) {x | f x = b} * qFail ok)
    (E : Set B) (n : ℕ) :
    pr (retry ok n) {x | f x ∈ E ∨ ok x = false} ≤
      pr (unif A) {x | f x ∈ E} + qFail ok ^ (n + 1) := by
  refine (pr_union_le _ {x | f x ∈ E} {x | ok x = false}).trans
    (add_le_add (le_of_eq ?_) (le_of_eq (pr_retry_fail ok n)))
  have h1 : pr (retry ok n) {x | f x ∈ E} = pr ((retry ok n).map f) E := (pr_map _ _ _).symm
  have h2 : pr (unif A) {x | f x ∈ E} = pr ((unif A).map f) E := (pr_map _ _ _).symm
  rw [h1, h2, map_retry ok f ind n]

end Prob
