-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P5.lean: a closed fact by Lean's kernel, alone in its file: piece 5 of
the rotary table's digest: blocks 1280 to 1535: the words 40960 to 49151.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p5 : (goL t1T 256 1280 T5 (bytesOf ropeW 40960 8192)).1 = T6 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p5
