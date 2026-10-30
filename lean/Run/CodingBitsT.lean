-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingBitsT.lean: from bits to bytes in a loop: a tail-recursive form of `bitsToBytes`
(Run/CodingBits.lean) for long strings, proved equal.

Two definitions that compute, two theorems, guards (tests that run while the file compiles).

Why: `bytesL` (Run/CodingBits.lean) puts each byte in front of the bytes of the rest: one frame of
the evaluator's stack a byte. Observed (in another part of this work): on the bits of a string of
some 77,000 bytes Lean's evaluator ended with "deep recursion". Here the bytes are pushed onto an
array, and the call on the rest is the last thing that is done.

Main names:
  `bytesGo_eq`, `bitsToBytesT_eq : bitsToBytesT l = bitsToBytes l`.
  A guard: from the bits of 200,000 bytes these bytes come back, byte for byte.

Limits: `bitsToBytes` itself is untouched, because proofs in other files read its text. One file
uses this one: Run/CodingThinX.lean [not in this library] (`toBytesT`).
-/
import Run.CodingBits

set_option autoImplicit false

namespace Run

/-- The bytes of a bit string pushed behind an array; a last group of fewer than eight bits is
filled up with 0. -/
def bytesGo : List Bool → Array UInt8 → Array UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r, acc =>
    bytesGo r (acc.push (byteOf [b0, b1, b2, b3, b4, b5, b6, b7]))
  | [], acc => acc
  | l, acc => acc.push (byteOf l)

def bitsToBytesT (l : List Bool) : ByteArray := ⟨bytesGo l #[]⟩

theorem bytesGo_eq (l : List Bool) :
    ∀ acc : Array UInt8, bytesGo l acc = acc ++ (bytesL l).toArray := by
  fun_induction bytesL l with
  | case1 b0 b1 b2 b3 b4 b5 b6 b7 r ih =>
      intro acc
      rw [bytesGo, ih]
      simp
  | case2 =>
      intro acc
      simp [bytesGo]
  | case3 l h1 h2 =>
      intro acc
      rw [bytesGo]
      · simp
      · exact h1
      · exact h2

theorem bitsToBytesT_eq (l : List Bool) : bitsToBytesT l = bitsToBytes l := by
  unfold bitsToBytesT bitsToBytes
  rw [bytesGo_eq]
  simp

#guard (bitsToBytesT (bytesToBits (_root_.Fmt.pattern 40))).data == (_root_.Fmt.pattern 40).data
#guard (bitsToBytesT [true, false, false, false, false, false, false, false, false, true]).data == #[1, 2]
#guard (bitsToBytesT (bytesToBits (_root_.Fmt.pattern 200000))).data == (_root_.Fmt.pattern 200000).data

end Run
