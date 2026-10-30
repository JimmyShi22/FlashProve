-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Fs/P2.lean: a closed fact by Lean's kernel, alone in its file: piece 2 of
table FS's digest: blocks 512 to 767: the words 16384 to 24575.

-/
import Johnson.Unfolds.Fs.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Fs
open Run.Blake2b

theorem p2 : (goL t1T 256 512 T2 (bytesOf fsW 16384 8192)).1 = T3 := by
  decide +kernel

end Johnson.Unfolds.Fs

#print axioms Johnson.Unfolds.Fs.p2
