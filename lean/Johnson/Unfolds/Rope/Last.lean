-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/Last.lean: two closed facts by Lean's kernel: the last call of the compression
function for the rotary table's digest (block 4095: the last 32 words), and the 32 bytes.

-/
import Johnson.Unfolds.Rope.States

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.Unfolds.Rope
open Run.Blake2b

theorem last :
    (compress (setLastblock { T16 with t0 := UInt64.ofNat (4 * 131072), t1 := t1T })
      (blkL (bytesOf ropeW 131040 32)).1).h = H := by
  decide +kernel

theorem bytes_H : H.bytes 32 = D := by
  decide +kernel

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.last
#print axioms Johnson.Unfolds.Rope.bytes_H
