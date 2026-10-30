-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DisciplineWorld.lean: one inequality in ℝ≥0∞: for natural numbers M ≤ B and a ≤ b,
M · a / 2^k ≤ B · b / 2^k (`term_le`, private to this file).
-/
import Compile.DisciplineCounts
import Compile.DisciplineOpen

namespace Compile.Disc
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

section Sum
variable (p : Params) (n : ℕ)

private theorem term_le {M a B b : ℕ} (k : ℕ) (hM : M ≤ B) (ha : a ≤ b) :
    (M : ℝ≥0∞) * (a : ℕ) / 2 ^ k ≤ (B : ℝ≥0∞) * (b : ℕ) / 2 ^ k := by
  have h1 : (M : ℝ≥0∞) ≤ B := by exact_mod_cast hM
  have h2 : (a : ℝ≥0∞) ≤ b := by exact_mod_cast ha
  gcongr

end Sum

end Compile.Disc
