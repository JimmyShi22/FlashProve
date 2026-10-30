-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
The number m of the statement on agreement is `bchksM` (Cb/Gen/CodeListRS.lean).


`Cb.Bridge.bchks46` proves that statement (Cb/Bridge, from files adapted
from ArkLib and Mathlib (lean/LIMITS.md, L15)); this
file does not apply that proof: that statement's count stands in the errors as a number.
Cb/Ref/GlRefNumMca.lean: **The own count of the statement on agreement from the paper cited in the
head of Cb/Gen/CodeListRS.lean (that file: bchksBound), bounded from above by general lemmas.**



In standard terms: general inequalities on one term of the
round-by-round error numbers of a proximity test (an interactive test that oracle words are close to
a code): for length n, degree bound k and radius e of a Reed-Solomon code the
formula `bchksBound n k e`, which the statement on agreement (`BCHKS46`, Cb/Gen/CodeListRS.lean)
gives as its bound on the number of exceptional coefficients, is bounded from above.


General lemmas. Arithmetic only: no code, no
protocol occurs here; that statement itself is neither used nor proved in this file.

Main names:
  `bchksM_le`, `bchksBound_le`: let s₁ and s₂ bound the square root of k / n from below and from
    above (given by their squares), and let m ≥ 3 be a whole number with s₂ ≤ m (1 - s₂ - e / n).
    Under the hypotheses on signs of the two lemmas, `bchksM n k e` (the number that the statement
    on agreement calls m) is at most m, and `bchksBound n k e` is at most the closed form on the
    right-hand side of `bchksBound_le`.
  `floor_of_bound`: for a count ≥ 0: count · 2^x ≤ q ⇒ (the count rounded down, which is what stands
    in the errors) · 2^x ≤ q.




















Limits: this file does not say that `bchksBound n k e` is the count of a whole round: a fold's round
adds its mask codes' counts and (list) · (masking degree - 1). It says nothing on a
factor for rows or for several tables, where a construction has one.

Terms: lean/GLOSSARY.md.

-/
import Cb.Gen.CodeListRS
import Cb.Gl.GlField

set_option autoImplicit false

namespace Cb

theorem bchksM_le (n k e m : ℕ) (s₂ : ℝ) (h2 : (k : ℝ) / n ≤ s₂ ^ 2) (hs2 : 0 ≤ s₂)
    (hpos : 0 < 1 - s₂ - (e : ℝ) / n) (hm : s₂ ≤ m * (1 - s₂ - (e : ℝ) / n)) (h3 : 3 ≤ m) :
    bchksM n k e ≤ m := by
  unfold bchksM
  have hs : Real.sqrt ((k : ℝ) / n) ≤ s₂ := Real.sqrt_le_iff.2 ⟨hs2, h2⟩
  have hd : 0 < 1 - Real.sqrt ((k : ℝ) / n) - (e : ℝ) / n := by linarith
  have hr : Real.sqrt ((k : ℝ) / n) / (1 - Real.sqrt ((k : ℝ) / n) - (e : ℝ) / n) ≤
      ((m : ℤ) : ℝ) := by
    rw [div_le_iff₀ hd]
    have h4 : (m : ℝ) * (1 - s₂ - (e : ℝ) / n) ≤ m * (1 - Real.sqrt ((k : ℝ) / n) - (e : ℝ) / n) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg m)
    push_cast
    linarith
  refine max_le ?_ (by exact_mod_cast h3)
  have h5 : ⌈Real.sqrt ((k : ℝ) / n) / (1 - Real.sqrt ((k : ℝ) / n) - (e : ℝ) / n)⌉ ≤ (m : ℤ) :=
    Int.ceil_le.2 hr
  exact_mod_cast h5

theorem bchksBound_le (n k e m : ℕ) (s₁ s₂ : ℝ) (hn : 0 < n) (hk : 0 < k) (hs1 : 0 < s₁)
    (h1 : s₁ ^ 2 ≤ (k : ℝ) / n) (h2 : (k : ℝ) / n ≤ s₂ ^ 2) (hs2 : 0 ≤ s₂)
    (hpos : 0 < 1 - s₂ - (e : ℝ) / n) (hm : s₂ ≤ m * (1 - s₂ - (e : ℝ) / n)) (h3 : 3 ≤ m) :
    bchksBound n k e ≤
      (2 * ((m : ℝ) + 1 / 2) ^ 5 + 3 * ((m : ℝ) + 1 / 2) * ((e : ℝ) / n) * ((k : ℝ) / n)) /
          (3 * (((k : ℝ) / n) * s₁)) * n +
        ((m : ℝ) + 1 / 2) / s₁ := by
  have hM := bchksM_le n k e m s₂ h2 hs2 hpos hm h3
  have hM0 : (0 : ℝ) ≤ bchksM n k e := le_trans (by norm_num) (le_max_right _ _)
  have hs : s₁ ≤ Real.sqrt ((k : ℝ) / n) := (Real.le_sqrt' hs1).2 h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hρ : (0 : ℝ) < (k : ℝ) / n := div_pos hk' hn'
  unfold bchksBound
  gcongr

theorem floor_of_bound (B : ℝ) (x q : ℕ) (h0 : 0 ≤ B) (h : B * 2 ^ x ≤ q) : ⌊B⌋₊ * 2 ^ x ≤ q := by
  have h1 : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le h0
  have h2 : ((⌊B⌋₊ * 2 ^ x : ℕ) : ℝ) ≤ q := by
    push_cast
    exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) h
  exact_mod_cast h2

theorem bchksBound_nonneg (n k e : ℕ) : 0 ≤ bchksBound n k e := by
  have hM0 : (0 : ℝ) ≤ bchksM n k e := le_trans (by norm_num) (le_max_right _ _)
  unfold bchksBound
  positivity

end Cb
