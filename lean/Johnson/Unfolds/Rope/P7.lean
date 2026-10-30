-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P7.lean: a closed fact by Lean's kernel, alone in its file: piece 7 of
the rotary table's digest: blocks 1792 to 2047: the words 57344 to 65535.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p7 : (goL t1T 256 1792 T7 (bytesOf ropeW 57344 8192)).1 = T8 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p7
