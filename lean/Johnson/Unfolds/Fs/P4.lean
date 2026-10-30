-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Fs/P4.lean: a closed fact by Lean's kernel, alone in its file: piece 4 of
table FS's digest: blocks 1024 to 1279: the words 32768 to 40959.

-/
import Johnson.Unfolds.Fs.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Fs
open Run.Blake2b

theorem p4 : (goL t1T 256 1024 T4 (bytesOf fsW 32768 8192)).1 = T5 := by
  decide +kernel

end Johnson.Unfolds.Fs

#print axioms Johnson.Unfolds.Fs.p4
