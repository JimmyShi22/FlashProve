-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P14.lean: a closed fact by Lean's kernel, alone in its file: piece 14 of
the rotary table's digest: blocks 3584 to 3839: the words 114688 to 122879.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p14 : (goL t1T 256 3584 T14 (bytesOf ropeW 114688 8192)).1 = T15 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p14
