-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OracleBits.lean: the single oracle `rom 256` (Rom/OSpec.lean), a function on all bit strings,
realised by the format's single oracle on byte strings.

Definitions that compute, theorems. That oracle takes every bit string; the format's
(Fmt/Rules23.lean: `oracle`) every byte string. The bit strings that are whole bytes already cover
all byte strings, so the others need room: one more escape.

Main names:
  `toBytes s`: the bytes of s, if s is whole bytes and its first byte is not 4; else the byte 4,
    the byte (length of s mod 8), the bytes of s filled up with zeros.
  `toBytes_plain`: a whole string whose first byte is not 4 goes to its own bytes: so every string
    of the format (first byte 0 or 1), and the strings that begin with one of the two escapes (the
    bytes 2, 3) of Run/CodingPage.lean's encoding, if they are whole.
  `toBytes_inj`: `toBytes` is one to one on all bit strings.
  `oBits : Fam (rom 256)`: the answer of the format's oracle at toBytes s, as 256 bits;
    `oBits_bytes`: at the bits of a byte string whose first byte is not 4: the format's oracle at
    that string.

Limits: this file does not say that the format's oracle behaves like a random function: the
instance's assumption.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingBitsLaws
import Fmt.Rules23
import Rom.Family

set_option autoImplicit false

namespace Run
open Rom

/-- Whole bytes, and the first byte is not the escape (the byte 4). -/
def plainB (s : List Bool) : Bool := whole s && !(s.take 8 == bitsOfByte 4)

/-- The bit string filled up with zeros to whole bytes. -/
def fillUp (s : List Bool) : List Bool := s ++ List.replicate ((8 - s.length % 8) % 8) false

def toBytes (s : List Bool) : ByteArray :=
  if plainB s then bitsToBytes s else ⟨#[4, UInt8.ofNat (s.length % 8)]⟩ ++ bitsToBytes (fillUp s)

theorem toBytes_plain (s : List Bool) (h : plainB s = true) : toBytes s = bitsToBytes s := if_pos h

theorem whole_fillUp (s : List Bool) : whole (fillUp s) = true := by
  refine (whole_iff _).2 ⟨(s.length + (8 - s.length % 8) % 8) / 8, ?_⟩
  unfold fillUp
  rw [List.length_append, List.length_replicate]
  omega

theorem bits_toBytes_plain (s : List Bool) (h : plainB s = true) : bytesToBits (toBytes s) = s := by
  rw [toBytes_plain s h]
  unfold plainB at h
  rw [Bool.and_eq_true] at h
  exact bytesToBits_bitsToBytes s h.1

theorem bits_toBytes_esc (s : List Bool) (h : plainB s = false) :
    bytesToBits (toBytes s) =
      bitsOfByte 4 ++ (bitsOfByte (UInt8.ofNat (s.length % 8)) ++ fillUp s) := by
  unfold toBytes
  rw [if_neg (by rw [h]; exact Bool.false_ne_true), bytesToBits_append,
    bytesToBits_bitsToBytes _ (whole_fillUp s)]
  show (bitsOfByte 4 ++ (bitsOfByte (UInt8.ofNat (s.length % 8)) ++ [])) ++ fillUp s = _
  rw [List.append_nil, List.append_assoc]

theorem not_plain_of_esc (s r : List Bool) (h : s = bitsOfByte 4 ++ r) : plainB s = false := by
  unfold plainB
  have h8 : s.take 8 = bitsOfByte 4 := by rw [h]; exact List.take_left' (length_bitsOfByte 4)
  rw [h8]
  simp

/-- `toBytes` is one to one on all bit strings. -/
theorem toBytes_inj (s t : List Bool) (h : toBytes s = toBytes t) : s = t := by
  have hb : bytesToBits (toBytes s) = bytesToBits (toBytes t) := congrArg bytesToBits h
  cases hs : plainB s with
  | true =>
      cases ht : plainB t with
      | true => rwa [bits_toBytes_plain s hs, bits_toBytes_plain t ht] at hb
      | false =>
          rw [bits_toBytes_plain s hs, bits_toBytes_esc t ht] at hb
          rw [not_plain_of_esc s _ hb] at hs
          cases hs
  | false =>
      cases ht : plainB t with
      | true =>
          rw [bits_toBytes_esc s hs, bits_toBytes_plain t ht] at hb
          rw [not_plain_of_esc t _ hb.symm] at ht
          cases ht
      | false =>
          rw [bits_toBytes_esc s hs, bits_toBytes_esc t ht] at hb
          have h1 := List.append_cancel_left hb
          have h2 : bitsOfByte (UInt8.ofNat (s.length % 8)) =
              bitsOfByte (UInt8.ofNat (t.length % 8)) :=
            List.append_inj_left h1 (by rw [length_bitsOfByte, length_bitsOfByte])
          have h3 : fillUp s = fillUp t :=
            List.append_inj_right h1 (by rw [length_bitsOfByte, length_bitsOfByte])
          have h4 : UInt8.ofNat (s.length % 8) = UInt8.ofNat (t.length % 8) := by
            rw [← byteOf_bits (UInt8.ofNat (s.length % 8)), h2, byteOf_bits]
          have h5 : s.length % 8 = t.length % 8 := by
            have := congrArg UInt8.toNat h4
            rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at this
            omega
          have h6 : s.length = t.length := by
            have := congrArg List.length h3
            unfold fillUp at this
            rw [List.length_append, List.length_append, List.length_replicate,
              List.length_replicate, h5] at this
            omega
          unfold fillUp at h3
          exact List.append_inj_left h3 h6

/-- The one oracle on bits: the answer of the format's oracle at `toBytes s`, as 256 bits. -/
def oBits : Fam (rom 256) := fun _ s => bytesToDig (_root_.Fmt.oracle (toBytes s))

/-- At the bits of a byte string whose first byte is not 4 it is the format's oracle at that
string. -/
theorem oBits_bytes (b : ByteArray) (h : plainB (bytesToBits b) = true) :
    oBits () (bytesToBits b) = bytesToDig (_root_.Fmt.oracle b) := by
  show bytesToDig (_root_.Fmt.oracle (toBytes (bytesToBits b))) = _
  rw [toBytes_plain _ h, bitsToBytes_bytesToBits]

end Run
