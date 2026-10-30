-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P11.lean: a closed fact by Lean's kernel, alone in its file: piece 11 of
the rotary table's digest: blocks 2816 to 3071: the words 90112 to 98303.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p11 : (goL t1T 256 2816 T11 (bytesOf ropeW 90112 8192)).1 = T12 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p11
