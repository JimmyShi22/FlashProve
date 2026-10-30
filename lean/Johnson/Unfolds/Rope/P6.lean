-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P6.lean: a closed fact by Lean's kernel, alone in its file: piece 6 of
the rotary table's digest: blocks 1536 to 1791: the words 49152 to 57343.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p6 : (goL t1T 256 1536 T6 (bytesOf ropeW 49152 8192)).1 = T7 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p6
