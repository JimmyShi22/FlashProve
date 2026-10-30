-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.Spec
import Run.Blake2b.Hash
/-!
# Passages between structures and arrays

Spec.lean works with arrays of long words and arrays of bytes, and Compress.lean and Hash.lean with
structures and ByteArray. This file has the passages between a chaining value (ChainingValue) or a block (MessageBlock)
as a structure and as an array of long words.
-/
namespace Run.Blake2b

/-- A chaining value as the array h of eight long words in Spec.lean's blake2b_state. -/
def ChainingValue.arr (s : ChainingValue) : Array UInt64 := #[s.h0, s.h1, s.h2, s.h3, s.h4, s.h5, s.h6, s.h7]

/-- The chaining value of an array's first eight long words; a word that the array lacks counts as
zero. -/
def ChainingValue.ofArr (h : Array UInt64) : ChainingValue := ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!, h[5]!, h[6]!, h[7]!⟩

/-- A block as the array m of sixteen long words in Spec.blake2b_compress. -/
def MessageBlock.arr (b : MessageBlock) : Array UInt64 :=
  #[b.m0, b.m1, b.m2, b.m3, b.m4, b.m5, b.m6, b.m7, b.m8, b.m9, b.m10, b.m11, b.m12, b.m13, b.m14,
    b.m15]

/-- The block of an array's first sixteen long words; a word that the array lacks counts as zero, as
it does where Spec.G reads an entry of m. -/
def MessageBlock.ofArr (m : Array UInt64) : MessageBlock :=
  ⟨m[0]!, m[1]!, m[2]!, m[3]!, m[4]!, m[5]!, m[6]!, m[7]!, m[8]!, m[9]!, m[10]!, m[11]!, m[12]!,
   m[13]!, m[14]!, m[15]!⟩

end Run.Blake2b
