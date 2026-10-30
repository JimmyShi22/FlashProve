-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P15.lean: a closed fact by Lean's kernel, alone in its file: piece 15 of
the rotary table's digest: blocks 3840 to 4094: the words 122880 to 131039.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p15 : (goL t1T 255 3840 T15 (bytesOf ropeW 122880 8160)).1 = T16 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p15
