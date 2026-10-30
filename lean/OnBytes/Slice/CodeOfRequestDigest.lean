-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CodeOfRequestDigest.lean: the bit string at which the random oracle is asked for the digest of a
request.

Why. The program takes a 32-byte digest of the request, which it forms with the second hash
function, into a proof's first hash call. In the experiment of the soundness statement the prover
chooses the request after it has seen answers of the oracle; such a prover is bounded in its queries
alone and computes for free, and a fixed compressing function HAS collisions. So that ONE call is
made a call of the random oracle too. This file fixes the string at which it is asked. The code
belongs to the experiment, not to the program: at the real hash functions the program's bytes do not
move.

The choice. The format's spelling of a hash call with a digest of 32 bytes (a first byte 0; the
parameter block with a start of 32 bytes; the label of number, tree and index; the bytes), under the
number 177, with s zero bytes behind the request. It is no leaf of the format: the label holds
neither a width nor the salt's length, the index is 0, and there is no fill. It has the form in
which a PAGE of the compiler writes a leaf: a start, a body, a salt. The format's page reserves that
number: no hash of the format is made under it, and it is left to a formal definition that needs
strings outside the format's image. In that form a page whose leaves' tags held 177 could write the
string as a leaf of a tree of depth 0, with a salt of the one length that all leaves have: no page
of today's type can, and no theorem here says it. That at today's pages it is a point of the spare
oracle is not shown in this library.

Main definition: `codeOld s w`. Main theorems: `codeOld_inj` (one to one in the request, AT ONE s:
`codeOld 40 (w ++ 16 zero bytes)` is `codeOld 56 w`); `codeOld_ne_oStr` (it is the string of no call
under another number: so of none of the format's, the calls 169 and 179 among them);
`codeOld_not_inImage` (its bytes lie outside the format's image in the library's own sense).

What is not claimed. That the second hash function behaves as a random oracle: that is the model.
Nothing ties this string to the program: no verifier that asks at it is written here. The library's
realised oracle answers a string outside the format's image by the format's hash under 177 of the
WHOLE string: at that point what is asked here is not the second hash function of w. And the bytes
that `codeOld s w` spells are the hash's input by which that realised oracle answers the RAW string
w with s zero bytes: whoever realises this call as the format's hash under 177 on these bytes makes
the two meet. The second hash function refuses some byte strings (too short; a length that is no
multiple of 4): whoever asks at `codeOld s w` must refuse there too.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.DigestPoint

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run

/-- The bit string at which the oracle is asked for the digest of a request. w: the request
file's bytes; s: the length of a leaf's salt in bytes. The format's spelling of a hash call under
the number 177, which the format reserves and never hashes under: half 0, tree 0, index 0, a start
of 32 zero bytes, then w and s zero bytes. -/
def codeOld (s : ℕ) (w : ByteArray) : List Bool :=
  bytesToBits (Fmt.oStr 0 177 0 0 Fmt.zero32 (w ++ Fmt.zeroBytes s))

/-- If a ++ z = b ++ z then a = b. -/
theorem append_right_cancel {a b z : ByteArray} (h : a ++ z = b ++ z) : a = b := by
  have h1 : (a ++ z).data.toList = (b ++ z).data.toList := by rw [h]
  rw [ByteArray.data_append, ByteArray.data_append, Array.toList_append, Array.toList_append] at h1
  exact ByteArray.ext (Array.ext' (List.append_cancel_right h1))

/-- It is one to one in the request, at one s. -/
theorem codeOld_inj (s : ℕ) {w w' : ByteArray} (h : codeOld s w = codeOld s w') : w = w' := by
  have h1 := bytesToBits_inj h
  have hz : Fmt.zero32.size = 32 := by decide
  have h2 := Fmt.oStr_bytes 0 177 0 0 Fmt.zero32 (w ++ Fmt.zeroBytes s) hz
  have h3 := Fmt.oStr_bytes 0 177 0 0 Fmt.zero32 (w' ++ Fmt.zeroBytes s) hz
  rw [h1] at h2
  exact append_right_cancel (h2.symm.trans h3)

/-- It is the string of no call under another number: either half, any tree number, index,
start and bytes. So it lies apart from every hash call of the format, which hashes under 177
nowhere. -/
theorem codeOld_ne_oStr (s : ℕ) (w : ByteArray) {n : ℕ} (hn : n % 65536 ≠ 177) (half : UInt8)
    (t i : ℕ) (st bs : ByteArray) : codeOld s w ≠ bytesToBits (Fmt.oStr half n t i st bs) := by
  intro h
  have h1 := bytesToBits_inj h
  have h2 := Tie.oStr_number 0 177 0 0 Fmt.zero32 (w ++ Fmt.zeroBytes s)
  rw [h1, Tie.oStr_number] at h2
  exact hn h2

/-- The bytes that it spells lie outside the format's image, in the library's own sense
(`Fmt.inImage`): read back as a string of the oracle they are none. So the library's realised oracle
answers them by the format's hash under 177 of the whole string (`Fmt.oracle_out`). -/
theorem codeOld_not_inImage (s : ℕ) (w : ByteArray) :
    Fmt.inImage (Fmt.oStr 0 177 0 0 Fmt.zero32 (w ++ Fmt.zeroBytes s)) = false := by
  unfold Fmt.inImage
  rcases hq : Fmt.oParse (Fmt.oStr 0 177 0 0 Fmt.zero32 (w ++ Fmt.zeroBytes s)) with _ | q
  · rfl
  · exfalso
    obtain ⟨hx, -, hd⟩ := Fmt.oStr_oParse _ q hq
    have h1 := Tie.oStr_number 0 177 0 0 Fmt.zero32 (w ++ Fmt.zeroBytes s)
    rw [hx, Tie.oStr_number] at h1
    unfold Fmt.hDom at hd
    simp only [Bool.and_eq_true] at hd
    have hn : Fmt.isNumber q.number = true := hd.1.1.1.1.1.1.1
    unfold Fmt.isNumber Fmt.numbers at hn
    simp only [List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
      decide_eq_true_eq] at hn
    rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at h1 <;>
      exact absurd h1 (by decide)

end OnBytes.Slice
