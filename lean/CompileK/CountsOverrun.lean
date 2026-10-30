-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/CountsOverrun.lean: a tail of the binomial distribution, and conditions on numbers for
the overrun term of ζ (`zetaBGen`, Compile/Batch/SpecHop.lean).




Statements and proofs. Generic: for any parameters p, but for `over_ref`, `over_ref_max` and the
third clause of `Over`.
ζ (`zetaBGen`, Compile/Batch/SpecHop.lean) has the term leaves · Pr[Bin(n, 1/leaves) > s1]: in n
calls, each of which draws one of the further encoded indices uniformly, some index is drawn more
than the s1 times that it bears. For n ≤ s1 it is 0 (`overrun_zero`, CompileK/Counts.lean). A
further encoded index is a further encoding of the index; `p.leaves` is their number.

Main names:
  `Prob.binTail_le_half_pow`: see its docstring.
  `Over p nMax`: nMax ≤ s1, or, for some m ≥ 220, 2 m ≤ s1 + 1 and 2 nMax² ≤ (m + 1) leaves², or
    s1 = 830,934 and nMax ≤ 808,850 · leaves (the sharper tail `pOver_leaves_le_400` of
    Prob/TailLeaves.lean, a certificate in natural numbers for every number of further encoded
    indices up to 2^21; `over_sharp`).

  `over_ref`, `over_ref_max`: at leaves = s1 = 830,934 Over holds for nMax = 2^25 (m = 4,096) and
    for nMax = 378,000,000 (m = 415,467) (the other terms of ζ that grow with n: Limits).

Why: in the proof of `binTail_le_half_pow` no number with an exponent of the size of s is
evaluated.
Why the third clause: with few further encoded indices the second clause gives nothing beyond s1
(at 2 of them and s1 = 830,934 it ends at 911 calls), while 1,000,000 uniform draws among 2 put
about 500,000 on each. The third clause admits 808,850 calls for each: 1,617,700 at 2.

Limits: the bound `binTail_le_half_pow` of the second clause is crude (a factor 2 for each pair of
draws, where the truth is far smaller). The third clause is stated at s1 = 830,934 only, the number
for which the certificate was computed: no statement of this library ties it to a protocol's
budget. This file says nothing on the other terms of ζ that grow with n.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Counts
import Prob.TailLeaves

set_option autoImplicit false

namespace Prob
open scoped ENNReal

/-- (2m)! ≥ (m + 1)^m: the upper half of the factors -/
theorem pow_le_factorial_two_mul (m : ℕ) : (m + 1) ^ m ≤ (2 * m).factorial := by
  have h := Nat.factorial_mul_pow_le_factorial (m := m) (n := m)
  rw [← two_mul] at h
  exact le_trans (Nat.le_mul_of_pos_left _ (Nat.factorial_pos m)) h

/-- C(n, 2m) · (m + 1)^m ≤ n^(2m) -/
theorem choose_mul_pow_le (n m : ℕ) : n.choose (2 * m) * (m + 1) ^ m ≤ n ^ (2 * m) := by
  have h1 : (2 * m).factorial * n.choose (2 * m) = n.descFactorial (2 * m) :=
    (Nat.descFactorial_eq_factorial_mul_choose n (2 * m)).symm
  calc
    n.choose (2 * m) * (m + 1) ^ m ≤ n.choose (2 * m) * (2 * m).factorial :=
      Nat.mul_le_mul_left _ (pow_le_factorial_two_mul m)
    _ = n.descFactorial (2 * m) := by rw [Nat.mul_comm, h1]
    _ ≤ n ^ (2 * m) := Nat.descFactorial_le_pow n (2 * m)

/-- The tail of the binomial distribution, far above the mean: for 0 < M and 1 ≤ m,
Pr[Bin(n, 1/M) > s] ≤ 2^-m whenever 2m ≤ s + 1 and 2 n² ≤ (m + 1) M². -/
theorem binTail_le_half_pow {M : ℕ} (hM : 0 < M) {n s m : ℕ} (hm : 1 ≤ m)
    (hs : 2 * m ≤ s + 1) (h : 2 * n ^ 2 ≤ (m + 1) * M ^ 2) :
    binTail n M s ≤ ((2 : ℝ≥0∞) ^ m)⁻¹ := by
  have h0 : binTail n M s ≤ binTail n M (2 * m - 1) := binTail_anti n M (by omega)
  have h1 := binTail_le_choose hM n (2 * m - 1)
  rw [show 2 * m - 1 + 1 = 2 * m by omega] at h1
  refine h0.trans (h1.trans ?_)
  -- C(n, 2m) · 2^m ≤ M^(2m)
  have h2 : n.choose (2 * m) * 2 ^ m ≤ M ^ (2 * m) := by
    have a : n.choose (2 * m) * 2 ^ m * (m + 1) ^ m ≤ M ^ (2 * m) * (m + 1) ^ m := by
      calc
        n.choose (2 * m) * 2 ^ m * (m + 1) ^ m = (n.choose (2 * m) * (m + 1) ^ m) * 2 ^ m := by ring
        _ ≤ n ^ (2 * m) * 2 ^ m := Nat.mul_le_mul_right _ (choose_mul_pow_le n m)
        _ = (2 * n ^ 2) ^ m := by rw [mul_pow, ← pow_mul, Nat.mul_comm]
        _ ≤ ((m + 1) * M ^ 2) ^ m := Nat.pow_le_pow_left h m
        _ = M ^ (2 * m) * (m + 1) ^ m := by rw [mul_pow, ← pow_mul, Nat.mul_comm]
    exact Nat.le_of_mul_le_mul_right a (Nat.pow_pos (Nat.succ_pos m))
  have h3 := natCast_div_le_div_of_pos (a := n.choose (2 * m)) (b := 1) (c := M ^ (2 * m))
    (d := 2 ^ m) (Nat.pow_pos hM) (Nat.pow_pos Nat.two_pos) (by rw [Nat.one_mul]; exact h2)
  simpa [Nat.cast_pow, one_div] using h3

end Prob

namespace Compile.Batch
open Iop Prob
open scoped ENNReal

/-- Conditions on numbers:
either no encoded index can be overrun in nMax calls, or the number of
calls lies far enough below leaves · s1. -/
def Over (p : Params) (nMax : ℕ) : Prop :=
  nMax ≤ p.s1 ∨ (∃ m, 220 ≤ m ∧ 2 * m ≤ p.s1 + 1 ∧ 2 * nMax ^ 2 ≤ (m + 1) * p.leaves ^ 2) ∨ (p.s1 = 830934 ∧ nMax ≤ 808850 * p.leaves)

/-- at leaves = s1 = 830,934: 2^25 calls -/
theorem over_ref : Over ⟨256, 256, 830933, 830934⟩ (2 ^ 25) :=
  Or.inr (Or.inl ⟨4096, by norm_num, by norm_num, by norm_num [Params.leaves]⟩)

/-- At the same parameters, as far as this bound goes: 378 million calls. -/
theorem over_ref_max : Over ⟨256, 256, 830933, 830934⟩ 378000000 :=
  Or.inr (Or.inl ⟨415467, by norm_num, by norm_num, by norm_num [Params.leaves]⟩)

/-- `Over` by its third clause: 808,850 calls for each further encoded index that bears 830,934,
whatever their number. -/
theorem over_sharp {p : Params} {nMax : ℕ} (hs : p.s1 = 830934) (hn : nMax ≤ 808850 * p.leaves) :
    Over p nMax :=
  Or.inr (Or.inr ⟨hs, hn⟩)

end Compile.Batch
