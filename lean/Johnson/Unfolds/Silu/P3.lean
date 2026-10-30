-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/P3.lean: a closed fact by Lean's kernel, alone in its file: piece 3 of table
SILU's digest: blocks 768 to 1023: the words 24576 to 32767.

-/
import Johnson.Unfolds.Silu.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Silu
open Run.Blake2b

theorem p3 : (goL t1S 256 768 T3 (bytesOf siluW 24576 8192)).1 = T4 := by
  decide +kernel

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.p3
