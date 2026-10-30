-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/P0.lean: a closed fact by Lean's kernel, alone in its file: piece 0 of table
SILU's digest: blocks 0 to 255: the words 0 to 8191.

-/
import Johnson.Unfolds.Silu.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Silu
open Run.Blake2b

theorem p0 : (goL t1S 256 0 (firstState 0 64) (bytesOf siluW 0 8192)).1 = T1 := by
  decide +kernel

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.p0
