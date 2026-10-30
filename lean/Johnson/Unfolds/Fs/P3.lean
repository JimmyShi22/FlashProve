-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Fs/P3.lean: a closed fact by Lean's kernel, alone in its file: piece 3 of
table FS's digest: blocks 768 to 1023: the words 24576 to 32767.

-/
import Johnson.Unfolds.Fs.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Fs
open Run.Blake2b

theorem p3 : (goL t1T 256 768 T3 (bytesOf fsW 24576 8192)).1 = T4 := by
  decide +kernel

end Johnson.Unfolds.Fs

#print axioms Johnson.Unfolds.Fs.p3
