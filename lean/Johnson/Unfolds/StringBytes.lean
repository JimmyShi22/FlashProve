-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/StringBytes.lean: LAWS ON LEAN's OWN LIBRARY: THE BYTES OF A STRING THAT IS MADE OF
A LIST OF CHARACTERS, WITHOUT THE PUSHES.
WHY. Lean's checker (its kernel) opens a String literal as `String.ofList ‹its characters›`, whose
bytes are `(cs.flatMap String.utf8EncodeChar).toByteArray`, and `List.toByteArray` pushes one byte
at a time onto an array that is a list: whoever makes the checker LOOK at these bytes pays the
square of their number, and a nest as deep as their number. These laws say what the bytes are;
nothing is left to reduce.
  `bytes_ofList`: `(String.ofList cs).toUTF8.data.toList = cs.flatMap String.utf8EncodeChar`.
  `chr`: the character with a byte's number. `enc_ofNat`: below 128 a character's bytes are its
    one number (128 cases, decided). `enc_chr`: the same at `chr b`. `flatMap_chr`: over a list.
  `bytes_of_ascii`: **`(String.ofList (p.map chr)).toUTF8.data.toList = p`** for every list p of
    bytes below 128.
The proofs call the library's own lemmas by name (String.toByteArray_ofList ·
List.data_toByteArray · UInt8.ofNat_toNat).
Limits. General laws; no file's bytes are named here. Nothing on soundness.
-/

namespace Johnson.Unfolds

/-- **The bytes of `String.ofList cs`.** -/
theorem bytes_ofList (cs : List Char) :
    (String.ofList cs).toUTF8.data.toList = cs.flatMap String.utf8EncodeChar := by
  show (String.ofList cs).toByteArray.data.toList = _
  rw [String.toByteArray_ofList, List.utf8Encode, List.data_toByteArray]

/-- The character with a byte's number. -/
def chr (b : UInt8) : Char := Char.ofNat b.toNat

/-- Below 128 a character's bytes are its one number. -/
theorem enc_ofNat : ∀ n, n < 128 → String.utf8EncodeChar (Char.ofNat n) = [UInt8.ofNat n] := by
  decide

theorem enc_chr (b : UInt8) (h : b < 128) : String.utf8EncodeChar (chr b) = [b] := by
  have h' : b.toNat < 128 := h
  rw [chr, enc_ofNat _ h', UInt8.ofNat_toNat]

theorem flatMap_chr (p : List UInt8) (h : p.all (· < 128) = true) :
    (p.map chr).flatMap String.utf8EncodeChar = p := by
  induction p with
  | nil => rfl
  | cons b t ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons, List.flatMap_cons, enc_chr b (of_decide_eq_true h.1), ih h.2]
    rfl

/-- **The bytes of a string made of bytes below 128.** -/
theorem bytes_of_ascii (p : List UInt8) (h : p.all (· < 128) = true) :
    (String.ofList (p.map chr)).toUTF8.data.toList = p := by
  rw [bytes_ofList, flatMap_chr p h]

end Johnson.Unfolds

#print axioms Johnson.Unfolds.bytes_ofList
#print axioms Johnson.Unfolds.enc_ofNat
#print axioms Johnson.Unfolds.enc_chr
#print axioms Johnson.Unfolds.flatMap_chr
#print axioms Johnson.Unfolds.bytes_of_ascii
