-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Rope/Chain.lean: the pieces joined: `state`: the list form of the second hash
function, at the number 72, of the 131,072 words of `ropeW` ends at `H`; `digestL`: its digest is
`D`. From `goL_step` (Johnson/Unfolds/SecondHashFunctionChain.lean) and the closed facts P0 … P15, Last.

-/
import Johnson.Unfolds.Rope.P0
import Johnson.Unfolds.Rope.P1
import Johnson.Unfolds.Rope.P2
import Johnson.Unfolds.Rope.P3
import Johnson.Unfolds.Rope.P4
import Johnson.Unfolds.Rope.P5
import Johnson.Unfolds.Rope.P6
import Johnson.Unfolds.Rope.P7
import Johnson.Unfolds.Rope.P8
import Johnson.Unfolds.Rope.P9
import Johnson.Unfolds.Rope.P10
import Johnson.Unfolds.Rope.P11
import Johnson.Unfolds.Rope.P12
import Johnson.Unfolds.Rope.P13
import Johnson.Unfolds.Rope.P14
import Johnson.Unfolds.Rope.P15
import Johnson.Unfolds.Rope.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Rope
open Run.Blake2b

/-- The table's bytes, cut. -/
theorem bytes_cut : bytesOf ropeW 0 131072 =
    bytesOf ropeW 0 8192 ++
      (bytesOf ropeW 8192 8192 ++
      (bytesOf ropeW 16384 8192 ++
      (bytesOf ropeW 24576 8192 ++
      (bytesOf ropeW 32768 8192 ++
      (bytesOf ropeW 40960 8192 ++
      (bytesOf ropeW 49152 8192 ++
      (bytesOf ropeW 57344 8192 ++
      (bytesOf ropeW 65536 8192 ++
      (bytesOf ropeW 73728 8192 ++
      (bytesOf ropeW 81920 8192 ++
      (bytesOf ropeW 90112 8192 ++
      (bytesOf ropeW 98304 8192 ++
      (bytesOf ropeW 106496 8192 ++
      (bytesOf ropeW 114688 8192 ++
      (bytesOf ropeW 122880 8160 ++
      (bytesOf ropeW 131040 32)))))))))))))))) := by
  rw [← bytesOf_append ropeW 8160 122880 32,
    ← bytesOf_append ropeW 8192 114688 8192,
    ← bytesOf_append ropeW 8192 106496 16384,
    ← bytesOf_append ropeW 8192 98304 24576,
    ← bytesOf_append ropeW 8192 90112 32768,
    ← bytesOf_append ropeW 8192 81920 40960,
    ← bytesOf_append ropeW 8192 73728 49152,
    ← bytesOf_append ropeW 8192 65536 57344,
    ← bytesOf_append ropeW 8192 57344 65536,
    ← bytesOf_append ropeW 8192 49152 73728,
    ← bytesOf_append ropeW 8192 40960 81920,
    ← bytesOf_append ropeW 8192 32768 90112,
    ← bytesOf_append ropeW 8192 24576 98304,
    ← bytesOf_append ropeW 8192 16384 106496,
    ← bytesOf_append ropeW 8192 8192 114688,
    ← bytesOf_append ropeW 8192 0 122880]

/-- The chain of 4,095 blocks. -/
theorem chain : goL t1T 4095 0 (firstState 0 64) (bytesOf ropeW 0 131072) =
    (T16, bytesOf ropeW 131040 32) := by
  rw [bytes_cut,
    goL_step ropeW t1T 256 3839 0 0 8192 _ T1 _ rfl p0,
    goL_step ropeW t1T 256 3583 256 8192 8192 _ T2 _ rfl p1,
    goL_step ropeW t1T 256 3327 512 16384 8192 _ T3 _ rfl p2,
    goL_step ropeW t1T 256 3071 768 24576 8192 _ T4 _ rfl p3,
    goL_step ropeW t1T 256 2815 1024 32768 8192 _ T5 _ rfl p4,
    goL_step ropeW t1T 256 2559 1280 40960 8192 _ T6 _ rfl p5,
    goL_step ropeW t1T 256 2303 1536 49152 8192 _ T7 _ rfl p6,
    goL_step ropeW t1T 256 2047 1792 57344 8192 _ T8 _ rfl p7,
    goL_step ropeW t1T 256 1791 2048 65536 8192 _ T9 _ rfl p8,
    goL_step ropeW t1T 256 1535 2304 73728 8192 _ T10 _ rfl p9,
    goL_step ropeW t1T 256 1279 2560 81920 8192 _ T11 _ rfl p10,
    goL_step ropeW t1T 256 1023 2816 90112 8192 _ T12 _ rfl p11,
    goL_step ropeW t1T 256 767 3072 98304 8192 _ T13 _ rfl p12,
    goL_step ropeW t1T 256 511 3328 106496 8192 _ T14 _ rfl p13,
    goL_step ropeW t1T 256 255 3584 114688 8192 _ T15 _ rfl p14,
    goL_step ropeW t1T 255 0 3840 122880 8160 _ T16 _ rfl p15, goL_zero]

theorem state : olderStateL 72 (4 * 131072) (bytesOf ropeW 0 131072) = H := by
  rw [olderStateL_eq 72 (4 * 131072) _ 131072 4095 t1T rfl rfl rfl, chain]
  exact last

theorem digestL : olderKL 72 (4 * 131072) ((fromTo ropeW 0 131072).flatMap w4) = D := by
  unfold olderKL
  rw [show (fromTo ropeW 0 131072).flatMap w4 = bytesOf ropeW 0 131072 from rfl, state, bytes_H]

end Johnson.Unfolds.Rope

#print axioms Johnson.Unfolds.Rope.bytes_cut
#print axioms Johnson.Unfolds.Rope.chain
#print axioms Johnson.Unfolds.Rope.state
#print axioms Johnson.Unfolds.Rope.digestL
