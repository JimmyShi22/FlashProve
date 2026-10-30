-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P10.lean: a closed fact by Lean's kernel, alone in its file: piece 10 of
the rotary table's digest: blocks 2560 to 2815: the words 81920 to 90111.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p10 : (goL t1T 256 2560 T10 (bytesOf ropeW 81920 8192)).1 = T11 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p10
