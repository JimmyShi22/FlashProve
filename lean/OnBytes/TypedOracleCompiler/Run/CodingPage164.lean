-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingPage164.lean.
Run/CodingPage164.lean: THE PARTIAL CODE OF A LEAF QUERY IN THE PROGRAMS' FORMAT. Definitions that
compute, with their laws. After the format page's rules R2.2, R2.4 (the oracle's strings), R7.3,
R7.4 (a leaf's bytes and digest), not held against the page as it ships; and by a rule
of this library that THE START OF A LEAF RIDES IN THE TYPED SALT: the first 256 bits of the
typed salt stand for the run's value, the rest is the file's salt.
GENERIC TOOLS.
   PCode.via p f g      a partial code carried to another type B along a partial reading f : B →
                        Option A with its section g : A → B
   pSalted pre n p      on (a, salt): written exactly if the salt has 256 + n bits and p writes a:
                        pre, the salt's first 256 bits, p's string of a, the salt's last n bits;
                        read back by cutting from both ends
THE LEAF.
   pre33                the 33 bytes with which the string of a call with a digest of 32 bytes
                        begins: the half 0; digest length, key length, fanout, depth; 28 zero bytes
   leafSel, leafMk      a leaf query whose body is a symbol of the protocol under the tag t (A
                        PARAMETER, read off the code p; Run/CodingFn.lean: castTag), as (symbol with
                        position, salt), and back
   pLeaf n p : PCode (LeafIn L)      from the bits n of the file's salt and A PARTIAL CODE p OF THE
                                     SYMBOLS WITH THEIR POSITIONS, which writes what stands between
                                     start and salt: the 16 bytes of the label (the leaves' number,
                                     the tree's number; 2^depth + position), the column, the fill
   pLeaf_pre            every string that it writes begins with pre33; pre33_not_prefix: so with the
                        byte 0
   oStr32_bits          the bits of the format's string of a call with a 32-byte digest and a start
                        of 32 bytes: pre33, the start, the label, the bytes: THE TIE of pLeaf's
                        strings to the format
WHAT IS NOT SAID. Which p: it is data of the toy protocol's wiring. The verifier tests only the
length of a typed salt: that its first 256 bits ARE the run's value is the parser's doing.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPage164
import Run.CodingPage166
import OnBytes.TypedOracleCompiler.Run.CodingFn
import OnBytes.TypedOracleCompiler.Compile.Batch.Oracles

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol
open _root_.Run

namespace PCode
variable {A B : Type}

end PCode

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag}

/-- TWO: a leaf query as (body, salt). (In the library: a leaf query on a symbol of the protocol
under the tag t; every other is no leaf of this page. Which bodies a page writes is the code p's
own matter.) -/
def leafSel (q : LeafIn L) : Option (L.Bd × List Bool) := some (q.body, q.salt)

def leafMk (x : L.Bd × List Bool) : LeafIn L := ⟨x.1, x.2⟩

theorem leafSel_mk (x : L.Bd × List Bool) : leafSel (leafMk x) = some x := rfl

theorem leafMk_sel (q : LeafIn L) (x : L.Bd × List Bool) (h : leafSel q = some x) :
    leafMk x = q := by
  cases h
  rfl

/-- A leaf query. -/
def pLeaf (n : ℕ) (p : PCode L.Bd) : PCode (LeafIn L) :=
  (pSalted pre33 n p).via leafSel leafMk leafSel_mk leafMk_sel

theorem pLeaf_pre (n : ℕ) (p : PCode L.Bd) (q : LeafIn L)
    (s : List Bool) (h : (pLeaf n p).put q = some s) : ∃ r, s = pre33 ++ r :=
  pSalted_pre pre33 n p (q.body, q.salt) s h

end TypedOracleCompiler.Run
