-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P13.lean: a closed fact by Lean's kernel, alone in its file: piece 13 of
the rotary table's digest: blocks 3328 to 3583: the words 106496 to 114687.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p13 : (goL t1T 256 3328 T13 (bytesOf ropeW 106496 8192)).1 = T14 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p13
