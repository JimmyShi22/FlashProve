-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Silu/Digest.lean: **the digest of the verifier's table SILU, at the stored example's
numbers, is 32 written bytes**: `silu_digest`: `secondHashFunction 72` of the bytes that `tableHeld` and
`tableHeldO` make of `(gateTables 8 4095 p3 gcl).1` is `D` (States.lean).
How. `tableDigest_list` (the fold of appends is a flat list; the hash is read off its head);
`silu_list` (the table is the stored words); the chain of 2,047 blocks cut into eight pieces
(`goL_step`), each a closed fact by Lean's kernel in a file of its own (P0 … P7); the last call and
the 32 bytes (Last.lean).
Limits. At the numbers 8 and 4095 alone. That the stored full-size files give these numbers, and
that `D` is what the parameter file's words `tsilu` spell, is not said here.

-/
import Johnson.Unfolds.Silu.Join
import Johnson.Unfolds.Silu.P0
import Johnson.Unfolds.Silu.P1
import Johnson.Unfolds.Silu.P2
import Johnson.Unfolds.Silu.P3
import Johnson.Unfolds.Silu.P4
import Johnson.Unfolds.Silu.P5
import Johnson.Unfolds.Silu.P6
import Johnson.Unfolds.Silu.P7
import Johnson.Unfolds.Silu.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Silu
open Run.Blake2b OnBytes.Model.Layer

/-- The table's bytes, cut. -/
theorem bytes_cut : bytesOf siluW 0 65536 =
    bytesOf siluW 0 8192 ++ (bytesOf siluW 8192 8192 ++ (bytesOf siluW 16384 8192 ++
      (bytesOf siluW 24576 8192 ++ (bytesOf siluW 32768 8192 ++ (bytesOf siluW 40960 8192 ++
        (bytesOf siluW 49152 8192 ++ (bytesOf siluW 57344 8160 ++
          bytesOf siluW 65504 32))))))) := by
  rw [← bytesOf_append siluW 8160 57344 32, ← bytesOf_append siluW 8192 49152 8192,
    ← bytesOf_append siluW 8192 40960 16384, ← bytesOf_append siluW 8192 32768 24576,
    ← bytesOf_append siluW 8192 24576 32768, ← bytesOf_append siluW 8192 16384 40960,
    ← bytesOf_append siluW 8192 8192 49152, ← bytesOf_append siluW 8192 0 57344]

/-- The chain of 2,047 blocks. -/
theorem chain : goL t1S 2047 0 (firstState 0 64) (bytesOf siluW 0 65536) =
    (T8, bytesOf siluW 65504 32) := by
  rw [bytes_cut,
    goL_step siluW t1S 256 1791 0 0 8192 _ T1 _ rfl p0,
    goL_step siluW t1S 256 1535 256 8192 8192 _ T2 _ rfl p1,
    goL_step siluW t1S 256 1279 512 16384 8192 _ T3 _ rfl p2,
    goL_step siluW t1S 256 1023 768 24576 8192 _ T4 _ rfl p3,
    goL_step siluW t1S 256 767 1024 32768 8192 _ T5 _ rfl p4,
    goL_step siluW t1S 256 511 1280 40960 8192 _ T6 _ rfl p5,
    goL_step siluW t1S 256 255 1536 49152 8192 _ T7 _ rfl p6,
    goL_step siluW t1S 255 0 1792 57344 8160 _ T8 _ rfl p7, goL_zero]

theorem state : olderStateL 72 (4 * 65536) (bytesOf siluW 0 65536) = H := by
  rw [olderStateL_eq 72 (4 * 65536) _ 65536 2047 t1S rfl rfl rfl, chain]
  exact last

/-- **THE DIGEST OF TABLE SILU.** -/
theorem silu_digest (p3 gcl : Bool) :
    OnBytes.secondHashFunction 72 ((gateTables 8 4095 p3 gcl).1.foldl
                  (fun b x => b ++ OnBytes.word32 x) ByteArray.empty) = D := by
  rw [tableDigest_list, silu_size, silu_list]
  unfold olderKL
  rw [show (fromTo siluW 0 65536).flatMap w4 = bytesOf siluW 0 65536 from rfl, state, bytes_H]

end Johnson.Unfolds.Silu

#print axioms Johnson.Unfolds.Silu.bytes_cut
#print axioms Johnson.Unfolds.Silu.chain
#print axioms Johnson.Unfolds.Silu.state
#print axioms Johnson.Unfolds.Silu.silu_digest
