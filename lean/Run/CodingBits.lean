-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingBits.lean: bit strings and byte strings.

Definitions that compute, with guards (tests that run while the file compiles).
The one oracle of this library's definitions is a function on bit strings with answers of lam bits
(Rom/Family.lean); in this file lam is 256; the programs' format speaks of byte strings and digests
of 32 bytes.

The order of bits is that of Fmt/Rules1.lean (`bitAt`): bit i of a string is bit (i mod 8), counted
from the lowest, of byte (i div 8). With it "the first w bits of a block" are "the low w bits of its
first word" (w at most 64).

Main names:
  `bytesL l`: the bytes of a bit string, eight bits a byte; a last group of fewer than eight bits is
    filled up with 0 (`whole l` says whether there is one).
  `bitsToBytes l`: the same as a `ByteArray`.
  `bitsOfByte`, `bitsL`, `bytesToBits`: the way back.
  `digToBytes`, `bytesToDig`: a digest of 256 bits as 32 bytes, and back (of a shorter string:
    filled up with 0; of a longer one: its first 32 bytes).

Limits: no theorem in this file: that the two ways undo each other is guarded at examples only.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules1
import Iop.Wire

namespace Run

/-- The byte whose bits, lowest first, are the first eight of l (a shorter list is filled up with
0). -/
def byteOf (l : List Bool) : UInt8 :=
  (l.take 8).foldr (fun b acc => acc * 2 + (if b then 1 else 0)) 0

/-- The bytes of a bit string; a last group of fewer than eight bits is filled up with 0. -/
def bytesL : List Bool → List UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r =>
    byteOf [b0, b1, b2, b3, b4, b5, b6, b7] :: bytesL r
  | [] => []
  | l => [byteOf l]

def bitsToBytes (l : List Bool) : ByteArray := ⟨(bytesL l).toArray⟩

/-- The length is a multiple of 8. -/
def whole (l : List Bool) : Bool := l.length % 8 == 0

/-- The eight bits of a byte, lowest first. -/
def bitsOfByte (x : UInt8) : List Bool :=
  (List.range 8).map fun i => (x >>> UInt8.ofNat i) &&& 1 == 1

def bitsL (l : List UInt8) : List Bool := l.flatMap bitsOfByte

def bytesToBits (b : ByteArray) : List Bool := bitsL b.data.toList

/-- A digest as 32 bytes. -/
def digToBytes (d : Iop.Dig 256) : ByteArray := bitsToBytes (List.ofFn d)

/-- 32 bytes as a digest. -/
def bytesToDig (b : ByteArray) : Iop.Dig 256 := fun i => _root_.Fmt.bitAt b i.val

#guard (bitsToBytes (bytesToBits (_root_.Fmt.pattern 40))).data == (_root_.Fmt.pattern 40).data
#guard (digToBytes (bytesToDig (_root_.Fmt.pattern 32))).data == (_root_.Fmt.pattern 32).data
#guard bytesL [true, false, false, false, false, false, false, false, false, true] == [1, 2]
#guard bitsOfByte 5 == [true, false, true, false, false, false, false, false]
#guard whole (bytesToBits (_root_.Fmt.pattern 3)) && !whole [true]
#guard (List.range 256).all fun n => byteOf (bitsOfByte (UInt8.ofNat n)) == UInt8.ofNat n

end Run
