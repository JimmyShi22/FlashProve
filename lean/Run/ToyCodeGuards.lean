-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyCodeGuards.lean: the toy's encoding runs: its strings are the format's, at examples. The toy
is that of Run/ToyQ.lean (`Run.Toy1`: this library's own, not the programs').

Tests only (#guard: evaluations made while the file compiles; they leave no theorem).
The family over a single oracle of Run/ToyCode.lean (`mT`) is evaluated at typed queries of the four
kinds, and each string is held against the format's own spelling of the call (`oStr`,
Fmt/Rules23.lean), written out here field by field after the format page, in an edition that is
not the one that ships (R2.4, R3.1, R4.6, R5.2, R5.4, R7.3, R7.4, R7.7; a leaf's label:
`Fmt.leafPlace`, as in a second edition of the format page, not held against the page that
ships):
   a node; a leaf; the first chain query (the block of the chain value); round 1 (8 bits of work):
   the three blocks: test block, chain value, message block; round 2 (no work): chain value, two
   message blocks;
   what does not fit goes behind the byte 2: a node of 255 bits; a leaf with a salt of another
   length; the message blocks of round 0; a round 3; a root in round 2;
   a spare string: a call under the number of the parameters' digest is written as itself; a string
   that begins with the byte 3 gets one more byte 3;
   the inverse runs: reading a string back and writing it again gives the string, at the ten strings
   of the last tests.

Limits: nothing is proved here. No hash is called.

Terms: lean/GLOSSARY.md.
-/
import Run.ToyCode

set_option autoImplicit false

namespace Run.Toy1.G
open Iop Rom Compile Compile.Batch

def cfg : ByteArray := _root_.Fmt.pattern 32 5 1
def m : OracleCoding (spec 256 2 Lt) 256 := mT cfg rfl

def cNode (q : Bits × Bits) : List Bool := m.code .node q (0 : Fin 1)
def cLeaf (q : LeafIn Lt) : List Bool := m.code .leaf q (0 : Fin 1)
def cFb (q : FbIn 256 Lt .test) (j : Fin 3) : List Bool := m.code (.fb .test) q j
def cOther (s : List Bool) : List Bool := m.code .other s (0 : Fin 1)

def bts (b : ByteArray) : List Bool := bytesToBits b
def hx (l : List Bool) : String := _root_.Fmt.hex (bitsToBytes l)
def dg (b : ByteArray) : Dig 256 := bytesToDig b

def dl : ByteArray := _root_.Fmt.pattern 32
def dr : ByteArray := _root_.Fmt.pattern 32 11 2
def rho : ByteArray := _root_.Fmt.pattern 32 13 4
def run : ByteArray := _root_.Fmt.pattern 32 3 9
def salt : ByteArray := _root_.Fmt.pattern 40 9 5
def e1 : E3 := (4, 5, 6)

-- a node
#guard hx (cNode (bts dl, bts dr)) == _root_.Fmt.hex (_root_.Fmt.oStr 0 166 0 0 cfg (dl ++ dr))
-- a leaf at position 9
def lq : LeafIn Lt := ⟨some (.inr ⟨.test, ⟨.inr (.inl (9 : Fin 16)), e1⟩⟩), bts run ++ bts salt⟩
#guard hx (cLeaf lq) == _root_.Fmt.hex (_root_.Fmt.oStr 0 164 (_root_.Fmt.leafPlace 0 3 5) 25 run (_root_.Fmt.ext e1 ++ salt))
-- the first chain query
def q0 : FbIn 256 Lt .test := ⟨0, .f1 [dg dl] (some e1) (bts run), none, .inl (.inr ())⟩
#guard hx (cFb q0 2) == _root_.Fmt.hex (_root_.Fmt.oStr 0 160 0 7 _root_.Fmt.zero32 (_root_.Fmt.firstBytes dl (stmB e1) ByteArray.empty (some run)))
-- round 1: a root, the nonce 378, 8 bits of work
def q1 : FbIn 256 Lt .test := ⟨1, .f2 none (bts rho), some (dg dr), .inr (.inl (.inr ((), 378)))⟩
def tail1 (c : Nat) : ByteArray :=
  dr ++ _root_.Fmt.u64n (4 + 256 * 8 + 65536 * c) ++ _root_.Fmt.u64n 378
#guard hx (cFb q1 0) == _root_.Fmt.hex (_root_.Fmt.oStr 0 162 7 1 rho (tail1 0))
#guard hx (cFb q1 2) == _root_.Fmt.hex (_root_.Fmt.oStr 1 162 7 1 rho (tail1 0))
#guard hx (cFb q1 1) == _root_.Fmt.hex (_root_.Fmt.oStr 0 162 7 1 rho (tail1 1))
-- round 2: an element in plain, no work
def q2 : FbIn 256 Lt .test := ⟨2, .f2 none (bts rho), none, .inr (.inr (.inl (.inr e1)))⟩
def tail2 (c : Nat) : ByteArray :=
  _root_.Fmt.ext e1 ++ _root_.Fmt.u64n (7 + 65536 * c) ++ _root_.Fmt.u64n 0
#guard hx (cFb q2 2) == _root_.Fmt.hex (_root_.Fmt.oStr 0 162 7 2 rho (tail2 0))
#guard hx (cFb q2 0) == _root_.Fmt.hex (_root_.Fmt.oStr 1 162 7 2 rho (tail2 0))
#guard hx (cFb q2 1) == _root_.Fmt.hex (_root_.Fmt.oStr 0 162 7 2 rho (tail2 1))

-- what does not fit: behind the byte 2
def first8 (l : List Bool) : List Bool := l.take 8
#guard first8 (cNode ((bts dl).take 255, bts dr)) == bitsOfByte 2
#guard first8 (cLeaf ⟨lq.body, bts run ++ bts dl⟩) == bitsOfByte 2
#guard first8 (cFb q0 0) == bitsOfByte 2
#guard first8 (cFb q0 1) == bitsOfByte 2
#guard first8 (cFb ⟨3, q2.head, none, q2.plain⟩ 0) == bitsOfByte 2
#guard first8 (cFb ⟨2, q2.head, some (dg dr), q2.plain⟩ 0) == bitsOfByte 2

-- spare strings
def s169 : List Bool := bts (_root_.Fmt.oStr 0 169 0 1 _root_.Fmt.zero32 (_root_.Fmt.pattern 50))
#guard cOther s169 == s169
#guard cOther [true, false, true] == [true, false, true]
#guard cOther (bitsOfByte 3 ++ cNode (bts dl, bts dr)) == bitsOfByte 3 ++ (bitsOfByte 3 ++ cNode (bts dl, bts dr))
#guard cOther (cNode (bts dl, bts dr)) == bitsOfByte 3 ++ cNode (bts dl, bts dr)

-- the inverse runs
def again (s : List Bool) : List Bool := m.code (m.inv s).1 (m.inv s).2.1 (m.inv s).2.2
#guard again (cNode (bts dl, bts dr)) == cNode (bts dl, bts dr)
#guard again (cLeaf lq) == cLeaf lq
#guard again (cFb q0 2) == cFb q0 2
#guard again (cFb q1 1) == cFb q1 1
#guard again (cFb q2 0) == cFb q2 0
#guard again (cFb q0 0) == cFb q0 0
#guard again s169 == s169
#guard again [] == []
#guard again (bitsOfByte 3) == bitsOfByte 3
#guard again (bitsOfByte 2) == bitsOfByte 2

end Run.Toy1.G
