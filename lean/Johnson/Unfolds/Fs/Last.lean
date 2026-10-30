-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Fs/Last.lean: two closed facts by Lean's kernel: the last call of the compression
function for table FS's digest (block 2047: the last 32 words), and the 32 bytes.

-/
import Johnson.Unfolds.Fs.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Fs
open Run.Blake2b

theorem last :
    (compress (setLastblock { T8 with t0 := UInt64.ofNat (4 * 65536), t1 := t1T })
      (blkL (bytesOf fsW 65504 32)).1).h = H := by
  decide +kernel

theorem bytes_H : H.bytes 32 = D := by
  decide +kernel

end Johnson.Unfolds.Fs

#print axioms Johnson.Unfolds.Fs.last
#print axioms Johnson.Unfolds.Fs.bytes_H
