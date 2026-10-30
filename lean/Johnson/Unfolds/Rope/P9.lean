-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P9.lean: a closed fact by Lean's kernel, alone in its file: piece 9 of
the rotary table's digest: blocks 2304 to 2559: the words 73728 to 81919.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p9 : (goL t1T 256 2304 T9 (bytesOf ropeW 73728 8192)).1 = T10 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p9
