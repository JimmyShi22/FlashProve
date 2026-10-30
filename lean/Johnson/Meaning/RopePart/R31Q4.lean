-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/RopePart/R31Q4.lean: one evaluation in Lean's kernel: the test partOK
(Johnson/Meaning/RopeFine.lean) at pair 31 of the 64 pairs of channels and the 128 tokens from
512 on. Some seconds. Made by program, one file for each pair and each eighth of the tokens.
-/
import Johnson.Meaning.RopeFine

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Meaning.Rope

theorem part_31_4 : partOK 31 4 = true := by decide +kernel

end Meaning.Rope
