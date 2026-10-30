-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/PackedIsMsg.lean

The packed arrays of Johnson/HonestTrace/Packed.lean against the library's messages "msgOf".

Johnson/Goal/Meaning/HidPack.lean packs a family of 25 lists of integers into messages over the
challenge field E, one message for each label, to show that premises on the library's reader of
packed messages can be met. This file shows that an entry of such a message is the image in E of the
entry of "packedOf", where the sizes agree.

Main theorems:
* "packTot_eq_pack3": the packing inside "msgOf", at the radix 2^20, is "pack3".
* "msgOf_eq_packedOf": if the sizes s have the radix 2^20 at the sub-proof that a label names, and
  there the rows of the entry that the label names are S's, then at a column below S's columns the
  message's entry (i, c) is the image in E of "packedOf S T" at that sub-proof's number, that
  entry's number, i and c.

Limits. This file lies under Johnson/Goal/ because "msgOf" does; it states no goal. The two premises
on the sizes s are not shown here of any s: that sizes which follow the Lean verifier's plans have
S's rows is a matter of the plans' shapes. "msgOf" lays one message for each label; by its own
file's word these are not the byte format's messages. From S's columns on "packedOf" is 0 and
"msgOf" goes on packing what T has there; the two are not compared there.

Not claimed: that a prover's messages are these; that a verifier accepts anything.

-/
import Johnson.Goal.Meaning.HidPack
import Johnson.HonestTrace.Packed

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Meaning (msgOf packTot ownerK ownerA)

/-- The library's packing of the first m entries of a column, at the radix 2^20, is "pack3". -/
theorem packTot_eq_pack3 (m : ℕ) (col : ℕ → ℤ) (i : ℕ) :
    packTot (2 ^ 20) m col i = pack3 m col i :=
  (pack3_eq_pack m col i).symm

/-- **An entry of "msgOf" is the image of an entry of "packedOf".** If at the sub-proof that the
label lab names the sizes s have the radix 2^20, and the rows of the entry that lab names are S's
rows of the matrix with these numbers: at a column c below S's columns, the entry (i, c) of the
message with the number lab, in either sort of row (mask row or main row: "msgOf" does not read that
argument), is the image in E of "packedOf S T" at these numbers, i and c. -/
theorem msgOf_eq_packedOf (S : Sz) (s : ℕ → Cb.Pv.Tail.Size) (T : ℕ → ℕ → ℕ → ℕ → ℤ) (lab : ℕ)
    (b : Bool) (i c : ℕ) (hr : (s (ownerK lab)).rad = 2 ^ 20)
    (hm : (s (ownerK lab)).m (ownerA lab) = (S.shapeNo (ownerK lab) (ownerA lab)).1)
    (hc : c < (S.shapeNo (ownerK lab) (ownerA lab)).2) :
    msgOf s T lab b i c =
      algebraMap Cb.Gl.F Cb.Gl.E (packedOf S T (ownerK lab) (ownerA lab) i c) := by
  unfold msgOf packedOf
  rw [if_pos hc, hr, hm, map_intCast,
    show (((2 ^ 20 : ℕ) : ℕ) : ℤ) = 2 ^ 20 by norm_num, packTot_eq_pack3]

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.packTot_eq_pack3
#print axioms OnBytes.HonestTrace.msgOf_eq_packedOf
