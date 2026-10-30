-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.Hash
/-!
# Theorems on Hash.lean: a message in one formula, the fast read, the digest's bytes

The main statements:

* message_eq: the last state of a message in one formula: all blocks but the last, then the last
  block with the number of bytes that are left.
* load64_eq_plain: a read with machine-word indices equals the plain read, for every array and every
  offset.
* data_store64, size_bytes64: the bytes that store64 adds, and that ChainingValue.bytes64 has 64 bytes.

Section 3 has small facts on reads with a default, for the files that import this one.

None is about RFC 7693 or blake2b-ref.c: they are about the definitions of Hash.lean only.

What "#print axioms" reports for message_eq, load64_eq_plain and size_bytes64: propext and
Quot.sound. There is no sorry and no axiom of ours.
Source. long8 writes out again, as an array, the eight bytes that store64 (Hash.lean) pushes, and
message_eq the text of message. These follow, at one remove, what Hash.lean names as its source.
Hash.lean's head says (its lines 10 to 13, copied here):
The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
-/
namespace Run.Blake2b

/-! ## 1. A message in one formula -/

/-- The last state of a message: all blocks but the last, then the last block with the number of
bytes that are left. The message has (inlen - 1) / 128 blocks before the last one. -/
theorem message_eq (blk : Nat → MessageBlock) (inlen : Nat) (S : State) :
    message blk inlen S =
      finalBlock (updateBlocks blk ((inlen - 1) / 128) 0 S) (blk ((inlen - 1) / 128))
        (inlen - 128 * ((inlen - 1) / 128)) := rfl

/-! ## 2. The read with machine-word indices equals the plain read -/

theorem ugetByte_eq (a : ByteArray) {k : Nat} (j : Nat)
    (hn : a.size.toUSize.toNat = a.size) (h : k + j < a.size) :
    ugetByte a k j hn h = byteOrZero a (k + j) := by
  unfold ugetByte byteOrZero
  rw [dif_pos h]
  show (a[(k.toUSize + USize.ofNat j).toNat]'(idx_lt j hn h)).toUInt64 = (a[k + j]).toUInt64
  simp only [toNat_toUSize_add j hn h]

theorem load64_eq_plain (a : ByteArray) (k : Nat) : load64 a k = load64Plain a k := by
  unfold load64
  split
  · rename_i hn
    split
    · rename_i h
      rw [ugetByte_eq a 0 hn (by omega), ugetByte_eq a 1 hn (by omega),
        ugetByte_eq a 2 hn (by omega), ugetByte_eq a 3 hn (by omega),
        ugetByte_eq a 4 hn (by omega), ugetByte_eq a 5 hn (by omega),
        ugetByte_eq a 6 hn (by omega), ugetByte_eq a 7 hn (by omega)]
      rfl
    · rfl
  · rfl

/-! ## 3. Reads with a default -/

theorem getD_of_lt {α : Type} {v : Array α} {p : Nat} {d : α} (h : p < v.size) :
    v.getD p d = v[p] := by
  unfold Array.getD; rw [dif_pos h]; rfl

theorem getD_of_ge {α : Type} {v : Array α} {p : Nat} {d : α} (h : ¬ p < v.size) :
    v.getD p d = d := by
  unfold Array.getD; rw [dif_neg h]

theorem byteOrZero_mk (x : Array UInt8) (i : Nat) :
    byteOrZero ⟨x⟩ i = (x.getD i 0).toUInt64 := by
  unfold byteOrZero
  by_cases h : i < x.size
  · rw [dif_pos (show i < (ByteArray.mk x).size from h), getD_of_lt h]; rfl
  · rw [dif_neg (show ¬ i < (ByteArray.mk x).size from h), getD_of_ge h]; rfl

/-- A read in front of the seam of two arrays in a row. -/
theorem getD_append_lt {a b : Array UInt8} {k : Nat} (h : k < a.size) :
    (a ++ b).getD k 0 = a.getD k 0 := by
  have h' : k < (a ++ b).size := by rw [Array.size_append]; omega
  rw [getD_of_lt h', getD_of_lt h, Array.getElem_append]
  split
  · rfl
  · rename_i hge
    exact absurd h hge

/-- A read at or after the seam. -/
theorem getD_append_ge {a b : Array UInt8} {k : Nat} (h : k < b.size) :
    (a ++ b).getD (a.size + k) 0 = b.getD k 0 := by
  have h' : a.size + k < (a ++ b).size := by rw [Array.size_append]; omega
  rw [getD_of_lt h', getD_of_lt h, Array.getElem_append]
  split
  · rename_i hlt
    omega
  · simp only [Nat.add_sub_cancel_left]

/-! ## 4. The digest's bytes -/

/-- The eight bytes of a long word, the least significant first. -/
def long8 (x : UInt64) : Array UInt8 :=
  #[x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8, (x >>> 32).toUInt8,
    (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]

theorem data_store64 (o : ByteArray) (x : UInt64) : (store64 o x).data = o.data ++ long8 x := by
  unfold store64 long8
  simp only [ByteArray.data_push]
  apply Array.toList_inj.mp
  simp

theorem size_bytes64 (s : ChainingValue) : s.bytes64.data.size = 64 := by
  unfold ChainingValue.bytes64
  simp only [data_store64, Array.size_append]
  rfl

end Run.Blake2b
