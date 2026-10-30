-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Blake2b/Test/Vectors.lean

Build-time tests of the fast BLAKE2b (Run/Blake2b/Hash.lean). Each test is a definition of type Bool
with a `#guard` line, so compiling this file runs it in Lean's interpreter. If one fails, the file
does not compile. Nothing imports this file; a build of all default targets compiles it.
Section 1: the example "abc" of RFC 7693, Appendix A. Sections 2 and 3: the 287 digests of
KnownAnswers.lean, from the hashlib of CPython 3.13.16. Section 4 tests the high word of the fast
function's counter: it compares parts of this library with one another and with six digests computed
with blake2b-ref.c. Section 5 compares parts of this library with one another. Section 6: lengths.
Limits: see "What these tests do not show" below.
-/
import Run.Blake2b.Test.KnownAnswers

namespace Run.Blake2b.Test

/-! ## What these tests do not show

- Of the expected digests only that of "abc" is cited to a printed text (RFC 7693, Appendix A). The
  six of `counterAnswers` (section 4) come from blake2b-ref.c of the BLAKE2 reference source code
  package. The text under test is adapted from that file, so they are not of another origin than it.
  All others come from the hashlib of CPython 3.13.16: see the limit in the head of
  KnownAnswers.lean. Values of another code origin: OtherOrigin.lean.
- But for these six digests, sections 4 to 6 have no value from outside this library. A fault that
  both sides of a comparison share is not noticed. In section 4 the two counter words are written
  out by hand, and the compression function `compress` is the same on both sides.
- No message of 2^64 bytes or more is hashed. Section 4 starts the function `message` at a count
  near or above 2^64, or near 2^128. The functions of Run/Blake2b/Hash.lean always start it at 0 or
  128; `resumeBytes` (Run/Blake2b/Salted.lean) starts it from the state that its caller gives.
- Section 4 runs the fast text only. No test reaches the carry into the high word of the plain
  definition's counter (`Spec.blake2b_increment_counter`, Run/Blake2b/Spec.lean).
- A `#guard` is run by Lean's interpreter, not checked by its kernel, and it is not a run of
  compiled code.
- That the fast function equals the plain definition for all arguments is a theorem
  (`blake2b_eq_spec_all`, Run/Blake2b/SpecThm.lean). These tests add examples with expected values;
  they prove nothing.
-/

/-! ## 1. RFC 7693, Appendix A: the example "abc" -/

/-- The three bytes "abc". -/
def abc : ByteArray := ⟨#[0x61, 0x62, 0x63]⟩

/-- The block of "abc": the three bytes, the first the least significant, then zeros. -/
def rfcA_block : Bool :=
  MessageBlock.ofBytes abc 0 == ⟨0x0000000000636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
#guard rfcA_block

/-- The last state: the 64 bytes of the digest below as eight words. -/
def rfcA_state : Bool :=
  (state ByteArray.empty abc 64).h ==
    ⟨0x0D4D1C983FA580BA, 0xE9F6129FB697276A, 0xB7C45A68142F214C, 0xD1A2FFDB6FBB124B,
    0x2D79AB2A39C5877D, 0x95CC3345DED552C2, 0x5A92F1DBA88AD318, 0x239900D4ED8623B9⟩
#guard rfcA_state

/-- BLAKE2b-512("abc"), the whole digest, as RFC 7693, Appendix A, gives it. -/
def rfcA_digest : Bool :=
  blake2b ByteArray.empty abc 64 == ⟨#[
    0xBA, 0x80, 0xA5, 0x3F, 0x98, 0x1C, 0x4D, 0x0D, 0x6A, 0x27, 0x97, 0xB6, 0x9F, 0x12, 0xF6, 0xE9,
    0x4C, 0x21, 0x2F, 0x14, 0x68, 0x5A, 0xC4, 0xB7, 0x4B, 0x12, 0xBB, 0x6F, 0xDB, 0xFF, 0xA2, 0xD1,
    0x7D, 0x87, 0xC5, 0x39, 0x2A, 0xAB, 0x79, 0x2D, 0xC2, 0x52, 0xD5, 0xDE, 0x45, 0x33, 0xCC, 0x95,
    0x18, 0xD3, 0x8A, 0xA8, 0xDB, 0xF1, 0x92, 0x5A, 0xB9, 0x23, 0x86, 0xED, 0xD4, 0x00, 0x99, 0x23]⟩
#guard rfcA_digest

/-! ## 2. The grid of keys, digest lengths and message lengths (KnownAnswers.lean) -/

/-- Every row of the grid: BLAKE2b of the message `ramp n 3` under the key `ramp k 5`, with a digest
of outlen bytes, is the digest in the table. -/
def knownGridAll : Bool :=
  knownGrid.all fun (k, outlen, n, d) =>
    blake2b (ramp k 5) (ramp n 3) outlen == hex d && (hex d).size == outlen
#guard knownGridAll
#guard knownGrid.length == 264

/-! ## 3. BLAKE2b-512 without a key, and other parameters (KnownAnswers.lean) -/

/-- BLAKE2b-512 of the message of n bytes is the digest in the table. -/
def known (n : Nat) : Bool :=
  match known512.lookup n with
  | none => false
  | some d => blake2b ByteArray.empty (pattern n) 64 == hex d && (hex d).size == 64
#guard known 0
#guard known 1
#guard known 63
#guard known 64
#guard known 127
#guard known 128
#guard known 129
#guard known 255
#guard known 256
#guard known 257
#guard known 1000
#guard known 4096
#guard known 65536

/-- The table's rows with a key or with a digest shorter than 64 bytes. -/
def knownOthers : Bool :=
  knownOther.all fun (k, outlen, n, d) =>
    blake2b (pattern k) (pattern n) outlen == hex d && (hex d).size == outlen
#guard knownOthers
#guard knownOther.length == 10

/-! ## 4. The counter's high word

No message of 2^64 bytes can be hashed in a test. These tests start `message` from a state whose
count is near or above 2^64, or near 2^128. They compare with calls of `compress` on states whose
two counter words are written out, and with digests computed with blake2b-ref.c. -/

/-- S with the counter words set to t0 and t1. Nothing is added to a counter here. -/
def withCount (S : State) (t0 t1 : UInt64) : State := { S with t0 := t0, t1 := t1 }

/-- The first state for a digest of 64 bytes and no key, with the counter words set to t0 and t1. -/
def startAt (t0 t1 : UInt64) : State := withCount (firstState 0 64) t0 t1

/-- Block i of the test message of 300 bytes. -/
def blk300 (i : Nat) : MessageBlock := MessageBlock.ofBytes (pattern 300) (128 * i)

/-- The test message of 300 bytes in three calls of `compress`. The counter words are a0 and a1 in
the first call, b0 and b1 in the second, c0 and c1 in the third, where f0 is set to all ones. -/
def byHand (a0 a1 b0 b1 c0 c1 : UInt64) : State :=
  let S := compress (startAt a0 a1) (blk300 0)
  let S := compress (withCount S b0 b1) (blk300 1)
  compress { withCount S c0 c1 with f0 := 0xFFFFFFFFFFFFFFFF } (blk300 2)

/-- `incrementCounter` carries. The low word comes to exactly 0 or passes it, and the high word goes
up by one; from its top it goes to 0. -/
def incrementCarries : Bool :=
  incrementCounter (startAt 0xFFFFFFFFFFFFFF80 0) 128 == startAt 0 1 &&
    incrementCounter (startAt 0xFFFFFFFFFFFFFFFF 0) 1 == startAt 0 1 &&
    incrementCounter (startAt 0xFFFFFFFFFFFFFFFF 7) 128 == startAt 127 8 &&
    incrementCounter (startAt 1 2) 0xFFFFFFFFFFFFFFFF == startAt 0 3 &&
    incrementCounter (startAt 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF) 1 == startAt 0 0
#guard incrementCarries

/-- `incrementCounter` just does not carry: the low word comes to 2^64 - 1, or nothing is added. -/
def incrementJustNot : Bool :=
  incrementCounter (startAt 0xFFFFFFFFFFFFFF7F 0) 128 == startAt 0xFFFFFFFFFFFFFFFF 0 &&
    incrementCounter (startAt 0xFFFFFFFFFFFFFFFE 9) 1 == startAt 0xFFFFFFFFFFFFFFFF 9 &&
    incrementCounter (startAt 0 2) 0xFFFFFFFFFFFFFFFF == startAt 0xFFFFFFFFFFFFFFFF 2 &&
    incrementCounter (startAt 0xFFFFFFFFFFFFFFFF 3) 0 == startAt 0xFFFFFFFFFFFFFFFF 3 &&
    incrementCounter (startAt 0 3) 0 == startAt 0 3
#guard incrementJustNot

/-- The count passes 2^64 inside the message: it starts at 2^64 - 200, and the counters are
2^64 - 72, 2^64 + 56 and 2^64 + 100. The second comparison has only the first two blocks, by
`updateBlocks`. -/
def counterCarry : Bool :=
  message blk300 300 (startAt 0xFFFFFFFFFFFFFF38 0) == byHand 0xFFFFFFFFFFFFFFB8 0 56 1 100 1 &&
    updateBlocks blk300 2 0 (startAt 0xFFFFFFFFFFFFFF38 0) ==
      compress (withCount (compress (startAt 0xFFFFFFFFFFFFFFB8 0) (blk300 0)) 56 1) (blk300 1)
#guard counterCarry

/-- The count starts at 2^64 - 128 and reaches exactly 2^64 at the end of the first block. -/
def counterExact : Bool :=
  message blk300 300 (startAt 0xFFFFFFFFFFFFFF80 0) == byHand 0 1 128 1 172 1
#guard counterExact

/-- A high word that is not 0 or 1 (the count starts at 5 * 2^64 + 7), and the count modulo 2^128
(it starts at 2^128 - 128, with the high word at its top). -/
def counterHigh : Bool :=
  message blk300 300 (startAt 7 5) == byHand 135 5 263 5 307 5 &&
    message blk300 300 (startAt 0xFFFFFFFFFFFFFF80 0xFFFFFFFFFFFFFFFF) == byHand 0 0 128 0 172 0
#guard counterHigh

/-- The count just does not pass 2^64: it starts at 2^64 - 301, and the counters are 2^64 - 173,
2^64 - 45 and 2^64 - 1. -/
def counterJustNot : Bool :=
  message blk300 300 (startAt 0xFFFFFFFFFFFFFED3 0) ==
    byHand 0xFFFFFFFFFFFFFF53 0 0xFFFFFFFFFFFFFFD3 0 0xFFFFFFFFFFFFFFFF 0
#guard counterJustNot

/-- The carry comes in the last block: the count starts at 2^64 - 300, and the counters are
2^64 - 172, 2^64 - 44 and exactly 2^64. -/
def counterLastBlock : Bool :=
  message blk300 300 (startAt 0xFFFFFFFFFFFFFED4 0) ==
    byHand 0xFFFFFFFFFFFFFF54 0 0xFFFFFFFFFFFFFFD4 0 0 1
#guard counterLastBlock

/-- The two counter words at the start, and the digest of 64 bytes of the test message of 300 bytes:
the six starts of the five tests of `message` above (`counterCarry` to `counterLastBlock`). The
digests were computed with blake2b_init, blake2b_update and blake2b_final of blake2b-ref.c (BLAKE2
reference source code package), with S->t[0] and S->t[1] set to the two words after blake2b_init. -/
def counterAnswers : List (UInt64 × UInt64 × String) := [
  (0xFFFFFFFFFFFFFF38, 0,
    "c13f24a675244be3f482ad2352e81cd3ba49707c158a538de48c6f58df20b1c1" ++
    "06cd60ff5d3299a0c3f8c6ea25add06c500850ebe6b4d865624bbf5a993df7b0"),
  (0xFFFFFFFFFFFFFF80, 0,
    "d340b493b475e6d7e0eda154eb1c64af14eb84de61df1ca6d9b34e3e2830b9a9" ++
    "a0837e8f13f1eeb25f2d1628f98a34b6fcca7b7f74d72bb7fd3e1c6e317215d9"),
  (7, 5,
    "7cb9c90167a6db392cf685b13b53ef9ff02e93a6078b7301072ed8f48eb51074" ++
    "58fb16001e678942c244cfa6f1ff61254ff21af6f0602d62945bcc67ac9e7f13"),
  (0xFFFFFFFFFFFFFF80, 0xFFFFFFFFFFFFFFFF,
    "f2ec06378bbcc63b64372cb2b2c2dd29ef2b8471a0208e3a5339d710dbb9262a" ++
    "c70de024a7be07b97f8f5113ed744e9322dd27b638c27b3738ad653bee14935d"),
  (0xFFFFFFFFFFFFFED3, 0,
    "f09d49a2564bf375da6eadde88357fa78f0d35f3128a46616da862b0df618fec" ++
    "57a8516fea077cd0c2ed16216600d8ae03a0fb358ea8e5f9ea023a690b88beeb"),
  (0xFFFFFFFFFFFFFED4, 0,
    "052a4fad5d1687e6bffa75eddf84b01e9076aa53130f34f5d798bb09dd525ad9" ++
    "68ec07526c8687fd01a42eec4113abb40867269cecd172a45b6d421a28006e93")]

/-- From each start the fast function comes to the digest in the table. -/
def counterReference : Bool :=
  counterAnswers.all fun (t0, t1, d) =>
    (message blk300 300 (startAt t0 t1)).h.bytes64 == hex d && (hex d).size == 64
#guard counterReference
#guard counterAnswers.length == 6

/-! ## 5. The number of blocks -/

/-- The messages of 0 and of 128 bytes are one block, that of 129 bytes is two, and that of 256
bytes is two. The counter words and the flag of each call of `compress` are written out. -/
def blockCounts : Bool :=
  state ByteArray.empty (pattern 0) 64 ==
      compress { startAt 0 0 with f0 := 0xFFFFFFFFFFFFFFFF } (MessageBlock.ofBytes (pattern 0) 0) &&
    state ByteArray.empty (pattern 128) 64 ==
      compress { startAt 128 0 with f0 := 0xFFFFFFFFFFFFFFFF } (MessageBlock.ofBytes (pattern 128) 0) &&
    state ByteArray.empty (pattern 129) 64 ==
      compress
        { withCount (compress (startAt 128 0) (MessageBlock.ofBytes (pattern 129) 0)) 129 0 with
          f0 := 0xFFFFFFFFFFFFFFFF }
        (MessageBlock.ofBytes (pattern 129) 128) &&
    state ByteArray.empty (pattern 256) 64 ==
      compress
        { withCount (compress (startAt 128 0) (MessageBlock.ofBytes (pattern 256) 0)) 256 0 with
          f0 := 0xFFFFFFFFFFFFFFFF }
        (MessageBlock.ofBytes (pattern 256) 128)
#guard blockCounts

/-! ## 6. Outside the range of lengths, and the lengths of digests -/

/-- A digest length of 0 or above 64 and a key of more than 64 bytes give the empty byte array. -/
def outside : Bool :=
  (blake2b ByteArray.empty abc 0).size == 0 && (blake2b ByteArray.empty abc 65).size == 0 &&
    (blake2b (pattern 65) abc 64).size == 0 && (blake2b (pattern 200) abc 32).size == 0
#guard outside

/-- Inside the range the digest has outlen bytes. -/
def lengths : Bool :=
  (List.range 64).all fun i => (blake2b ByteArray.empty abc (i + 1)).size == i + 1 &&
    (blake2b (pattern (i + 1)) abc (i + 1)).size == i + 1
#guard lengths

end Run.Blake2b.Test
