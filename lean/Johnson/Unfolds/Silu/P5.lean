-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/P5.lean: a closed fact by Lean's kernel, alone in its file: piece 5 of table
SILU's digest: blocks 1280 to 1535: the words 40960 to 49151.

-/
import Johnson.Unfolds.Silu.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Silu
open Run.Blake2b

theorem p5 : (goL t1S 256 1280 T5 (bytesOf siluW 40960 8192)).1 = T6 := by
  decide +kernel

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.p5
