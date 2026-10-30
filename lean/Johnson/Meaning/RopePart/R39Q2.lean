-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/RopePart/R39Q2.lean: one evaluation in Lean's kernel: the test partOK
(Johnson/Meaning/RopeFine.lean) at pair 39 of the 64 pairs of channels and the 128 tokens from
256 on. Some seconds. Made by program, one file for each pair and each eighth of the tokens.
-/
import Johnson.Meaning.RopeFine

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Meaning.Rope

theorem part_39_2 : partOK 39 2 = true := by decide +kernel

end Meaning.Rope
