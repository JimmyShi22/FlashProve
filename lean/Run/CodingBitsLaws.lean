-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingBitsLaws.lean: the conversions between bit strings and byte strings undo each other;
starting from a bit string they do so if its length is a multiple of 8.

Theorems on the definitions of Run/CodingBits.lean.

Main names:
  `byteOf_bits`, `bits_byteOf`: a byte and its eight bits (by evaluation of all 256 cases in the
    kernel).
  `bitsToBytes_bytesToBits`, `bytesToBits_bitsToBytes`: for `ByteArray`; `bytesL_bitsL`,
    `bitsL_bytesL`: for lists.

Limits: this file says nothing on digests as functions (`digToBytes`, `bytesToDig`).
-/
import Run.CodingBits
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace Run

theorem byteOf_bits_fin : ∀ n : Fin 256, byteOf (bitsOfByte (UInt8.ofNat n)) = UInt8.ofNat n := by
  decide +kernel

theorem byteOf_bits (x : UInt8) : byteOf (bitsOfByte x) = x := by
  have h := byteOf_bits_fin ⟨x.toNat, x.toNat_lt⟩
  simpa using h

theorem bits_byteOf :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      bitsOfByte (byteOf [b0, b1, b2, b3, b4, b5, b6, b7]) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  decide +kernel

theorem length_bitsOfByte (x : UInt8) : (bitsOfByte x).length = 8 := by simp [bitsOfByte]

/-- The eight bits of a byte, by name. -/
theorem bitsOfByte_eq (x : UInt8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, bitsOfByte x = [b0, b1, b2, b3, b4, b5, b6, b7] :=
  ⟨_, _, _, _, _, _, _, _, rfl⟩

theorem bytesL_bitsL : ∀ l : List UInt8, bytesL (bitsL l) = l
  | [] => rfl
  | x :: l => by
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hx⟩ := bitsOfByte_eq x
      show bytesL (bitsOfByte x ++ bitsL l) = x :: l
      rw [hx]
      show byteOf [b0, b1, b2, b3, b4, b5, b6, b7] :: bytesL (bitsL l) = x :: l
      rw [← hx, byteOf_bits, bytesL_bitsL l]

theorem bitsL_bytesL : ∀ (n : ℕ) (l : List Bool), l.length = 8 * n → bitsL (bytesL l) = l
  | 0, l, h => by
      have : l = [] := List.length_eq_zero_iff.1 (by omega)
      subst this
      rfl
  | n + 1, l, h => by
      match l, h with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r, h =>
          have hr : r.length = 8 * n := by simp only [List.length_cons] at h; omega
          show bitsOfByte (byteOf [b0, b1, b2, b3, b4, b5, b6, b7]) ++ bitsL (bytesL r) = _
          rw [bits_byteOf, bitsL_bytesL n r hr]
          rfl
      | [], h => simp at h
      | [_], h => simp at h; omega
      | [_, _], h => simp at h; omega
      | [_, _, _], h => simp at h; omega
      | [_, _, _, _], h => simp at h; omega
      | [_, _, _, _, _], h => simp at h; omega
      | [_, _, _, _, _, _], h => simp at h; omega
      | [_, _, _, _, _, _, _], h => simp at h; omega

theorem whole_iff (l : List Bool) : whole l = true ↔ ∃ n, l.length = 8 * n := by
  unfold whole
  rw [beq_iff_eq]
  constructor
  · intro h
    exact ⟨l.length / 8, by omega⟩
  · rintro ⟨n, h⟩
    omega

/-- Bytes, their bits, back. -/
theorem bitsToBytes_bytesToBits (b : ByteArray) : bitsToBytes (bytesToBits b) = b := by
  apply ByteArray.ext
  show (bytesL (bitsL b.data.toList)).toArray = b.data
  rw [bytesL_bitsL]

/-- Bits, their bytes, back, for a whole number of bytes (`h`). -/
theorem bytesToBits_bitsToBytes (l : List Bool) (h : whole l = true) :
    bytesToBits (bitsToBytes l) = l := by
  obtain ⟨n, hn⟩ := (whole_iff l).1 h
  show bitsL (bytesL l).toArray.toList = l
  rw [List.toList_toArray]
  exact bitsL_bytesL n l hn

theorem bitsL_append (a b : List UInt8) : bitsL (a ++ b) = bitsL a ++ bitsL b := List.flatMap_append

theorem bytesToBits_append (a b : ByteArray) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  show bitsL (a ++ b).data.toList = _
  rw [ByteArray.data_append, Array.toList_append, bitsL_append]
  rfl

theorem length_bitsL : ∀ l : List UInt8, (bitsL l).length = 8 * l.length
  | [] => rfl
  | x :: l => by
      show (bitsOfByte x ++ bitsL l).length = _
      rw [List.length_append, length_bitsOfByte, length_bitsL l, List.length_cons]
      omega

theorem length_bytesToBits (b : ByteArray) : (bytesToBits b).length = 8 * b.size := by
  show (bitsL b.data.toList).length = _
  rw [length_bitsL, Array.length_toList]
  rfl

theorem whole_bytesToBits (b : ByteArray) : whole (bytesToBits b) = true :=
  (whole_iff _).2 ⟨b.size, length_bytesToBits b⟩

theorem bytesToBits_inj {a b : ByteArray} (h : bytesToBits a = bytesToBits b) : a = b := by
  rw [← bitsToBytes_bytesToBits a, h, bitsToBytes_bytesToBits]

theorem size_bitsToBytes (l : List Bool) (n : ℕ) (h : l.length = 8 * n) :
    (bitsToBytes l).size = n := by
  have h1 := length_bytesToBits (bitsToBytes l)
  rw [bytesToBits_bitsToBytes l ((whole_iff l).2 ⟨n, h⟩)] at h1
  omega

end Run
