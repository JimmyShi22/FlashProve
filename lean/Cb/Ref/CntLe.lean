-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ref/CntLe.lean.
States: THE ONE GUARD OF A TABLE THAT WAS NOT DECIDABLE, MADE DECIDABLE. The count of the assumed
statement, Cb.bchksBound n k e (Cb/Gen/CodeListRS.lean), is a real number (a square root, a
ceiling).
(CntLe n k e m a b D N) ten inequalities BETWEEN NATURAL NUMBERS (a Decidable instance stands): a/D
and b/D bracket the square root of k/n from below and above; m is at least the statement's number m
at that bracket; N bounds the formula at (m, a/D).
(floor_le_of_cntLe) CntLe n k e m a b D N ⇒ ⌊bchksBound n k e⌋₊ ≤ N: ONE lemma at letters, by the
library's bchksBound_le (Cb/Ref/GlRefNumMca.lean).



Under: nothing. The assumed statement itself is neither used nor proved here: arithmetic on its
FORMULA.
Does not say: that agreement holds with that count; that (m, a, b) are the best brackets.
-/
import Cb.Ref.GlRefNumMca

set_option autoImplicit false

namespace Cb

/-- Ten inequalities between natural numbers. -/
def CntLe (n k e m a b D N : ℕ) : Prop :=
  0 < n ∧ 0 < k ∧ 0 < a ∧ 0 < D ∧ a ^ 2 * n ≤ k * D ^ 2 ∧ k * D ^ 2 ≤ b ^ 2 * n ∧
  b * n + e * D < D * n ∧ b * n + m * (b * n + e * D) ≤ m * (D * n) ∧ 3 ≤ m ∧
  D * ((2 * m + 1) ^ 5 * n ^ 2 + 24 * (2 * m + 1) * k * (e + 1)) ≤ 48 * k * a * N

instance (n k e m a b D N : ℕ) : Decidable (CntLe n k e m a b D N) := by
  unfold CntLe; infer_instance

theorem bound_le_of_cntLe {n k e m a b D N : ℕ} (h : CntLe n k e m a b D N) :
    bchksBound n k e ≤ N := by
  obtain ⟨hn, hk, ha, hD, h1, h2, hpos, hm, h3, hq⟩ := h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have c1 : (a : ℝ) ^ 2 * n ≤ k * (D : ℝ) ^ 2 := by exact_mod_cast h1
  have c2 : (k : ℝ) * (D : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 * n := by exact_mod_cast h2
  have c3 : (b : ℝ) * n + e * D < D * n := by exact_mod_cast hpos
  have c4 : (b : ℝ) * n + m * (b * n + e * D) ≤ m * (D * n) := by exact_mod_cast hm
  have c5 : (D : ℝ) * ((2 * m + 1) ^ 5 * n ^ 2 + 24 * (2 * m + 1) * k * (e + 1)) ≤
      48 * k * a * N := by exact_mod_cast hq
  have s1 : ((a : ℝ) / D) ^ 2 ≤ (k : ℝ) / n := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hn']
    exact c1
  have s2 : (k : ℝ) / n ≤ ((b : ℝ) / D) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hn' (by positivity)]
    exact c2
  have e3 : 1 - (b : ℝ) / D - (e : ℝ) / n = (D * n - b * n - e * D) / (D * n) := by
    field_simp
  have p3 : (0 : ℝ) < D * n - b * n - e * D := by linarith
  have s3 : 0 < 1 - (b : ℝ) / D - (e : ℝ) / n := by
    rw [e3]
    exact div_pos p3 (by positivity)
  have s4 : (b : ℝ) / D ≤ m * (1 - (b : ℝ) / D - (e : ℝ) / n) := by
    rw [e3, ← mul_div_assoc, div_le_div_iff₀ hD' (by positivity)]
    have c4' : (b : ℝ) * n ≤ m * (D * n - b * n - e * D) := by nlinarith [c4]
    nlinarith [mul_le_mul_of_nonneg_right c4' hD'.le]
  have hb := bchksBound_le n k e m ((a : ℝ) / D) ((b : ℝ) / D) hn hk (div_pos ha' hD') s1 s2
    (by positivity) s3 s4 h3
  refine le_trans hb ?_
  have e1 : (2 * ((m : ℝ) + 1 / 2) ^ 5 + 3 * ((m : ℝ) + 1 / 2) * ((e : ℝ) / n) * ((k : ℝ) / n)) /
          (3 * (((k : ℝ) / n) * ((a : ℝ) / D))) * n + ((m : ℝ) + 1 / 2) / ((a : ℝ) / D) =
      (D : ℝ) * ((2 * m + 1) ^ 5 * n ^ 2 + 24 * (2 * m + 1) * k * (e + 1)) / (48 * k * a) := by
    field_simp
    ring
  rw [e1, div_le_iff₀ (by positivity)]
  linarith

theorem floor_le_of_cntLe {n k e m a b D N : ℕ} (h : CntLe n k e m a b D N) :
    ⌊bchksBound n k e⌋₊ ≤ N :=
  Nat.floor_le_of_le (bound_le_of_cntLe h)

end Cb

#print axioms Cb.floor_le_of_cntLe
