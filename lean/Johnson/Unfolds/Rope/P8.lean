-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P8.lean: a closed fact by Lean's kernel, alone in its file: piece 8 of
the rotary table's digest: blocks 2048 to 2303: the words 65536 to 73727.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p8 : (goL t1T 256 2048 T8 (bytesOf ropeW 65536 8192)).1 = T9 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p8
