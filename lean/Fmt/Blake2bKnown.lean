-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Fmt.Blake2b
/-!
# Known answers of BLAKE2b, as theorems

Four digests of `blake2b`, computed by Lean's kernel. A change of a definition that alters one of
them makes this file fail to compile. The expected digests were computed with `hashlib.blake2b` of
CPython 3.13.
  `blake2b_abc`       the three bytes "abc", 64 bytes, no salt, no personalization
  `blake2b_empty32`   the empty message, 32 bytes, no salt, no personalization
  `blake2b_two32`     two blocks (the bytes 0, .., 255), 32 bytes, salt 0, .., 15, personalization
                      16, .., 31
  `blake2b_full64`    one full block (the bytes 0, .., 127), 64 bytes, the same salt and
                      personalization
At the end two tests of `Run.Blake2b.compress`. A test (#guard) is an evaluation made while the
file compiles; the compile fails if the result changes; it leaves no theorem. More such answers:
Run/Blake2b/Test/Salted.lean.
-/
namespace Fmt

namespace B2

/-- The bytes first, .., first + n - 1, modulo 256. -/
def count (first n : Nat) : ByteArray := ⟨(Array.range n).map fun i => (first + i).toUInt8⟩

end B2

namespace Spec

/-- The statement of `Fmt.blake2b_abc`. -/
def blake2b_abc : Prop :=
  (blake2b 64 ByteArray.empty ByteArray.empty ⟨#[0x61, 0x62, 0x63]⟩).data = #[
    0xba, 0x80, 0xa5, 0x3f, 0x98, 0x1c, 0x4d, 0x0d, 0x6a, 0x27, 0x97, 0xb6, 0x9f, 0x12, 0xf6, 0xe9,
    0x4c, 0x21, 0x2f, 0x14, 0x68, 0x5a, 0xc4, 0xb7, 0x4b, 0x12, 0xbb, 0x6f, 0xdb, 0xff, 0xa2, 0xd1,
    0x7d, 0x87, 0xc5, 0x39, 0x2a, 0xab, 0x79, 0x2d, 0xc2, 0x52, 0xd5, 0xde, 0x45, 0x33, 0xcc, 0x95,
    0x18, 0xd3, 0x8a, 0xa8, 0xdb, 0xf1, 0x92, 0x5a, 0xb9, 0x23, 0x86, 0xed, 0xd4, 0x00, 0x99, 0x23]

/-- The statement of `Fmt.blake2b_empty32`. -/
def blake2b_empty32 : Prop :=
  (blake2b 32 ByteArray.empty ByteArray.empty ByteArray.empty).data = #[
    0x0e, 0x57, 0x51, 0xc0, 0x26, 0xe5, 0x43, 0xb2, 0xe8, 0xab, 0x2e, 0xb0, 0x60, 0x99, 0xda, 0xa1,
    0xd1, 0xe5, 0xdf, 0x47, 0x77, 0x8f, 0x77, 0x87, 0xfa, 0xab, 0x45, 0xcd, 0xf1, 0x2f, 0xe3, 0xa8]

/-- The statement of `Fmt.blake2b_two32`. -/
def blake2b_two32 : Prop :=
  (blake2b 32 (B2.count 0 16) (B2.count 16 16) (B2.count 0 256)).data = #[
    0x38, 0x56, 0xf1, 0x27, 0xe5, 0xbe, 0x00, 0x4e, 0xa5, 0xa6, 0x0c, 0xc7, 0xcf, 0x99, 0x4b, 0x93,
    0xea, 0x76, 0x0e, 0x71, 0x52, 0x12, 0x3c, 0xa6, 0xb8, 0x17, 0xf8, 0x19, 0x51, 0x65, 0xf7, 0xa0]

/-- The statement of `Fmt.blake2b_full64`. -/
def blake2b_full64 : Prop :=
  (blake2b 64 (B2.count 0 16) (B2.count 16 16) (B2.count 0 128)).data = #[
    0xde, 0xce, 0x2c, 0x34, 0xa6, 0x35, 0x09, 0x08, 0xfa, 0xd7, 0xbf, 0x08, 0xab, 0x69, 0x7e, 0x2b,
    0xe7, 0x7d, 0xb6, 0x88, 0x8a, 0xc4, 0x54, 0x69, 0x33, 0x16, 0x26, 0x80, 0x22, 0xc6, 0xb9, 0x00,
    0x5e, 0x38, 0x14, 0x22, 0x96, 0x60, 0x55, 0x4b, 0xd7, 0x35, 0xa5, 0xeb, 0x93, 0xcf, 0xf4, 0xeb,
    0xa3, 0xc2, 0x3a, 0x2d, 0x13, 0xd9, 0xb5, 0xde, 0x1c, 0xf0, 0xf9, 0xb6, 0x69, 0xe3, 0x4a, 0xef]

end Spec

theorem blake2b_abc : Spec.blake2b_abc := by
  unfold Spec.blake2b_abc
  decide +kernel

theorem blake2b_empty32 : Spec.blake2b_empty32 := by
  unfold Spec.blake2b_empty32
  decide +kernel

theorem blake2b_two32 : Spec.blake2b_two32 := by
  unfold Spec.blake2b_two32
  decide +kernel

theorem blake2b_full64 : Spec.blake2b_full64 := by
  unfold Spec.blake2b_full64
  decide +kernel

-- The compression function: a message of one block is one call. The counter words and the two flags
-- of that call are written out.
#guard [0, 1, 64, 128].all fun n =>
  Run.Blake2b.compress
      { h := (Run.Blake2b.firstStateSalted 64 (B2.count 0 16) (B2.count 16 16)).h,
        t0 := UInt64.ofNat n, t1 := 0, f0 := 0xffffffffffffffff, f1 := 0 }
      (Run.Blake2b.MessageBlock.ofBytesPlain (B2.count 0 n) 0) ==
    Run.Blake2b.stateSalted (B2.count 0 16) (B2.count 16 16) (B2.count 0 n) 64

-- The compression function with the counter above 2^64 and without the last-block flag. The count
-- is 2^64 + 5: the low word is 5 and the high word 1. With c = 0x0101010101010101, word i of the
-- chaining value is c * i + 5 and word i of the block is c * 3 * i + 9, modulo 2^64. The expected
-- words were computed with blake2b_compress of blake2b-ref.c (BLAKE2 reference source code
-- package).
#guard
  let h (i : UInt64) : UInt64 := 0x0101010101010101 * i + 5
  let m (i : UInt64) : UInt64 := 0x0101010101010101 * 3 * i + 9
  let r := (Run.Blake2b.compress
    { h := ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩, t0 := 5, t1 := 1, f0 := 0, f1 := 0 }
    ⟨m 0, m 1, m 2, m 3, m 4, m 5, m 6, m 7, m 8, m 9, m 10, m 11, m 12, m 13, m 14, m 15⟩).h
  #[r.h0, r.h1, r.h2, r.h3, r.h4, r.h5, r.h6, r.h7] ==
  #[0x961d610c2c7b5b88, 0x9bcae6be5444467f, 0x094faf5671822495, 0x779550c155ba18d0,
    0xf2c80fe54d6f58d0, 0x1475e7b99b1706b7, 0x6726ed37070e97f9, 0xd2060dc95d89b6f7]

end Fmt

#print axioms Fmt.blake2b_abc
#print axioms Fmt.blake2b_empty32
#print axioms Fmt.blake2b_two32
#print axioms Fmt.blake2b_full64
