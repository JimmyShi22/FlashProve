-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Fs/P7.lean: a closed fact by Lean's kernel, alone in its file: piece 7 of
table FS's digest: blocks 1792 to 2046: the words 57344 to 65503.

-/
import Johnson.Unfolds.Fs.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Fs
open Run.Blake2b

theorem p7 : (goL t1T 255 1792 T7 (bytesOf fsW 57344 8160)).1 = T8 := by
  decide +kernel

end Johnson.Unfolds.Fs

#print axioms Johnson.Unfolds.Fs.p7
