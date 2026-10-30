-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/P6.lean: a closed fact by Lean's kernel, alone in its file: piece 6 of table
SILU's digest: blocks 1536 to 1791: the words 49152 to 57343.

-/
import Johnson.Unfolds.Silu.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Silu
open Run.Blake2b

theorem p6 : (goL t1S 256 1536 T6 (bytesOf siluW 49152 8192)).1 = T7 := by
  decide +kernel

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.p6
