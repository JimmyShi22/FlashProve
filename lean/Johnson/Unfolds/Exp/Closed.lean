-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Exp/Closed.lean: a closed fact by Lean's kernel, alone in its file: the list form of
the second hash function, at the number 72, of the 2,307 words of `expW` (9,228 bytes: 72 blocks and
a last one of 12 bytes) gives the 32 bytes `D`. The bytes were printed by Lean's evaluator.

-/
import Johnson.Unfolds.Exp.Def

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Exp

def D : ByteArray :=
  ⟨#[71, 19, 125, 217, 130, 74, 52, 143, 124, 78, 142, 249, 229, 227, 52, 31, 202, 96, 177,
    111, 161, 109, 94, 181, 152, 184, 228, 102, 56, 43, 218, 9]⟩

theorem digestL : olderKL 72 (4 * 2307) ((fromTo expW 0 2307).flatMap w4) = D := by
  decide +kernel

end Johnson.Unfolds.Exp

#print axioms Johnson.Unfolds.Exp.digestL
