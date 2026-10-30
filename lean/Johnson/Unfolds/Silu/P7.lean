-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/P7.lean: a closed fact by Lean's kernel, alone in its file: piece 7 of table
SILU's digest: blocks 1792 to 2046: the words 57344 to 65503.

-/
import Johnson.Unfolds.Silu.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Silu
open Run.Blake2b

theorem p7 : (goL t1S 255 1792 T7 (bytesOf siluW 57344 8160)).1 = T8 := by
  decide +kernel

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.p7
