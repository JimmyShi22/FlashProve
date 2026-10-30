-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LinkSound.lean: arithmetic for a bound at positions (`pow_mul_pow_le`): see its statement.
(Words of this library: lean/GLOSSARY.md.)
-/
import Iop.State
import Blocks.LowerKit
import Blocks.Wired
import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Blocks

open Iop Prob Finset

namespace Setup

variable {F : Type} [Field F] [Fintype F] {E : Type} [Field E] [Fintype E] [DecidableEq E]
    [Algebra F E]

variable {γ φ : ℕ → E}

/-! ## Positions -/

omit [Field F] [Fintype F] in
/-- Arithmetic for a bound at positions. -/
theorem pow_mul_pow_le {b' b n p p' m : ℕ} (hb : b' ≤ b) (hn : b' ≤ n) (hm : m ≤ p) :
    b' ^ p * n ^ p' ≤ b ^ m * n ^ (p + p' - m) := by
  have h1 : b' ^ p = b' ^ m * b' ^ (p - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have h2 : n ^ (p + p' - m) = n ^ (p - m) * n ^ p' := by
    rw [← pow_add]
    congr 1
    omega
  rw [h1, h2, mul_assoc]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hb m)
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn _))

end Setup

end Blocks
