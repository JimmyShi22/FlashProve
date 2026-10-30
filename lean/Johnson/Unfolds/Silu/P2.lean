-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/P2.lean: a closed fact by Lean's kernel, alone in its file: piece 2 of table
SILU's digest: blocks 512 to 767: the words 16384 to 24575.

-/
import Johnson.Unfolds.Silu.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Silu
open Run.Blake2b

theorem p2 : (goL t1S 256 512 T2 (bytesOf siluW 16384 8192)).1 = T3 := by
  decide +kernel

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.p2
