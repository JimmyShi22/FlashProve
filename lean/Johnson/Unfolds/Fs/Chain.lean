-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Fs/Chain.lean: the pieces joined: `state`: the list form of the second hash
function, at the number 72, of the 65,536 words of `fsW` ends at `H`; `digestL`: its digest is `D`.
From `goL_step` (Johnson/Unfolds/SecondHashFunctionChain.lean) and the closed facts P0 … P7, Last.

-/
import Johnson.Unfolds.Fs.P0
import Johnson.Unfolds.Fs.P1
import Johnson.Unfolds.Fs.P2
import Johnson.Unfolds.Fs.P3
import Johnson.Unfolds.Fs.P4
import Johnson.Unfolds.Fs.P5
import Johnson.Unfolds.Fs.P6
import Johnson.Unfolds.Fs.P7
import Johnson.Unfolds.Fs.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Fs
open Run.Blake2b

/-- The table's bytes, cut. -/
theorem bytes_cut : bytesOf fsW 0 65536 =
    bytesOf fsW 0 8192 ++
      (bytesOf fsW 8192 8192 ++
      (bytesOf fsW 16384 8192 ++
      (bytesOf fsW 24576 8192 ++
      (bytesOf fsW 32768 8192 ++
      (bytesOf fsW 40960 8192 ++
      (bytesOf fsW 49152 8192 ++
      (bytesOf fsW 57344 8160 ++
      (bytesOf fsW 65504 32)))))))) := by
  rw [← bytesOf_append fsW 8160 57344 32,
    ← bytesOf_append fsW 8192 49152 8192,
    ← bytesOf_append fsW 8192 40960 16384,
    ← bytesOf_append fsW 8192 32768 24576,
    ← bytesOf_append fsW 8192 24576 32768,
    ← bytesOf_append fsW 8192 16384 40960,
    ← bytesOf_append fsW 8192 8192 49152,
    ← bytesOf_append fsW 8192 0 57344]

/-- The chain of 2,047 blocks. -/
theorem chain : goL t1T 2047 0 (firstState 0 64) (bytesOf fsW 0 65536) =
    (T8, bytesOf fsW 65504 32) := by
  rw [bytes_cut,
    goL_step fsW t1T 256 1791 0 0 8192 _ T1 _ rfl p0,
    goL_step fsW t1T 256 1535 256 8192 8192 _ T2 _ rfl p1,
    goL_step fsW t1T 256 1279 512 16384 8192 _ T3 _ rfl p2,
    goL_step fsW t1T 256 1023 768 24576 8192 _ T4 _ rfl p3,
    goL_step fsW t1T 256 767 1024 32768 8192 _ T5 _ rfl p4,
    goL_step fsW t1T 256 511 1280 40960 8192 _ T6 _ rfl p5,
    goL_step fsW t1T 256 255 1536 49152 8192 _ T7 _ rfl p6,
    goL_step fsW t1T 255 0 1792 57344 8160 _ T8 _ rfl p7, goL_zero]

theorem state : olderStateL 72 (4 * 65536) (bytesOf fsW 0 65536) = H := by
  rw [olderStateL_eq 72 (4 * 65536) _ 65536 2047 t1T rfl rfl rfl, chain]
  exact last

theorem digestL : olderKL 72 (4 * 65536) ((fromTo fsW 0 65536).flatMap w4) = D := by
  unfold olderKL
  rw [show (fromTo fsW 0 65536).flatMap w4 = bytesOf fsW 0 65536 from rfl, state, bytes_H]

end Johnson.Unfolds.Fs

#print axioms Johnson.Unfolds.Fs.bytes_cut
#print axioms Johnson.Unfolds.Fs.chain
#print axioms Johnson.Unfolds.Fs.state
#print axioms Johnson.Unfolds.Fs.digestL
