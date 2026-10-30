-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/P12.lean: a closed fact by Lean's kernel, alone in its file: piece 12 of
the rotary table's digest: blocks 3072 to 3327: the words 98304 to 106495.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem p12 : (goL t1T 256 3072 T12 (bytesOf ropeW 98304 8192)).1 = T13 := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.p12
