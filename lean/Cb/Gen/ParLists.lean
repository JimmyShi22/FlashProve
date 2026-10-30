-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/ParLists.lean: the bound 2^-132 on a round-by-round error (`epsS`), and two lemmas from an
inequality of natural numbers to the form of `Iop.Err.Below`.

Main names:
  `epsS`, `below_of_mul_le`, `below_epsS`: see their docstrings.

Limits: this file says nothing on a protocol: which round of which block has which error is the
blocks' matter. No number here is a security level.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.ParCodes
import Iop.InteractiveOracleProof
noncomputable section -- markers lifted: Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Par
open Code Code.Circle
open scoped ENNReal

/-- The bound for every round-by-round error: the number 2^-132 (that a round has an error within it
is no statement of this file). -/
def epsS : ℝ≥0∞ := (2 ^ 132 : ℝ≥0∞)⁻¹

/-- From an inequality of natural numbers to the form of Iop.Err.Below. -/
theorem below_of_mul_le {a N x : ℕ} (h : a * 2 ^ x ≤ N) :
    (a : ℝ≥0∞) ≤ (2 ^ x : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞) := by
  have h2 : (2 ^ x : ℝ≥0∞) ≠ 0 := by positivity
  have h3 : (2 ^ x : ℝ≥0∞) ≠ ⊤ := by simp
  have h1 : (a : ℝ≥0∞) * 2 ^ x ≤ (N : ℝ≥0∞) := by exact_mod_cast h
  calc (a : ℝ≥0∞) = (2 ^ x : ℝ≥0∞)⁻¹ * ((a : ℝ≥0∞) * 2 ^ x) := by
        rw [mul_comm (a : ℝ≥0∞), ← mul_assoc, ENNReal.inv_mul_cancel h2 h3, one_mul]
    _ ≤ (2 ^ x : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞) := by gcongr

/-- If a · 2^x ≤ N with 132 ≤ x, then a ≤ `epsS` · N. -/
theorem below_epsS {a N x : ℕ} (hx : 132 ≤ x) (h : a * 2 ^ x ≤ N) :
    (a : ℝ≥0∞) ≤ epsS * (N : ℝ≥0∞) :=
  below_of_mul_le (le_trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by norm_num) hx)) h)

end Cb.Par
