-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P3.lean: a closed fact by Lean's kernel, alone in its file: piece 3 of
the rotary table's digest: blocks 768 to 1023: the words 24576 to 32767.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p3 : (goL t1T 256 768 T3 (bytesOf ropeW 24576 8192)).1 = T4 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p3
