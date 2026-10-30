-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/Last.lean: two closed facts by Lean's kernel: the last call of the compression
function for table SILU's digest (block 2,047: the words 65,504 to 65,535), and the 32 bytes.

-/
import Johnson.Unfolds.Silu.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Silu
open Run.Blake2b

theorem last :
    (compress (setLastblock { T8 with t0 := UInt64.ofNat (4 * 65536), t1 := t1S })
      (blkL (bytesOf siluW 65504 32)).1).h = H := by
  decide +kernel

theorem bytes_H : H.bytes 32 = D := by
  decide +kernel

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.last
#print axioms Johnson.Unfolds.Silu.bytes_H
