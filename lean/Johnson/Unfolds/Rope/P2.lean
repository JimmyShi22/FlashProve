-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P2.lean: a closed fact by Lean's kernel, alone in its file: piece 2 of
the rotary table's digest: blocks 512 to 767: the words 16384 to 24575.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p2 : (goL t1T 256 512 T2 (bytesOf ropeW 16384 8192)).1 = T3 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p2
