-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/P4.lean: a closed fact by Lean's kernel, alone in its file: piece 4 of table
SILU's digest: blocks 1024 to 1279: the words 32768 to 40959.

-/
import Johnson.Unfolds.Silu.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Silu
open Run.Blake2b

theorem p4 : (goL t1S 256 1024 T4 (bytesOf siluW 32768 8192)).1 = T5 := by
  decide +kernel

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.p4
