-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/RopePart/R52Q6.lean: one evaluation in Lean's kernel: the test partOK
(Johnson/Meaning/RopeFine.lean) at pair 52 of the 64 pairs of channels and the 128 tokens from
768 on. Some seconds. Made by program, one file for each pair and each eighth of the tokens.
-/
import Johnson.Meaning.RopeFine

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Meaning.Rope

theorem part_52_6 : partOK 52 6 = true := by decide +kernel

end Meaning.Rope
