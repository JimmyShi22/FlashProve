-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P1.lean: a closed fact by Lean's kernel, alone in its file: piece 1 of
the rotary table's digest: blocks 256 to 511: the words 8192 to 16383.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p1 : (goL t1T 256 256 T1 (bytesOf ropeW 8192 8192)).1 = T2 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p1
