-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/GrindSmall.lean: one lemma on several rounds in one (`two_wG`): see its statement. (Words of
this library: lean/GLOSSARY.md.)
Limits: nothing at concrete parameters; nothing on a compiled scheme.
-/
import Blocks.Grind
import Blocks.SmallRecut
import Iop.GrindRecut

set_option autoImplicit false

namespace Blocks
open Iop
open scoped ENNReal

/-! ## Several rounds in one -/

theorem two_wG {e1 e2 n1 n2 w m b1 b2 : ℕ}
    (h1 : e1 * m ≤ w * (2 ^ b1 * n1)) (h2 : e2 * m ≤ 2 ^ b2 * n2) :
    (e1 * n2 + n1 * e2) * m ≤ (w + 1) * (2 ^ max b1 b2 * (n1 * n2)) := by
  have p1 : 2 ^ b1 ≤ 2 ^ max b1 b2 := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have p2 : 2 ^ b2 ≤ 2 ^ max b1 b2 := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  calc (e1 * n2 + n1 * e2) * m = (e1 * m) * n2 + n1 * (e2 * m) := by ring
    _ ≤ (w * (2 ^ b1 * n1)) * n2 + n1 * (2 ^ b2 * n2) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ h1) (Nat.mul_le_mul_left _ h2)
    _ = w * (2 ^ b1 * (n1 * n2)) + 2 ^ b2 * (n1 * n2) := by ring
    _ ≤ w * (2 ^ max b1 b2 * (n1 * n2)) + 2 ^ max b1 b2 * (n1 * n2) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ p1)) (Nat.mul_le_mul_right _ p2)
    _ = (w + 1) * (2 ^ max b1 b2 * (n1 * n2)) := by ring

end Blocks
