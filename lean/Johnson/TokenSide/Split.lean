-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/Split.lean: the honest side of the second form as token programs: which part of an
oracle's answer is a secret string, the rules that the programs keep, and small tools. Definitions,
and two small lemmas.

The files of this folder write the compiled prover of one slot (proveX, OnBytes/Prover/Defs.lean),
a table's builder and the scheme with the whole key published (Johnson/WholeKey/Defs.lean) a second
time, in the language of Rom/Defer.lean, in which a secret string is a token. These programs are a
device of one step of a proof of index privacy (deferred programming, Rom.Spec.defer). They stand in
no statement on the scheme, and the scheme is not defined by them.

What is other than in the first form's Compile/Batch/Split.lean, whose pattern this file follows:
the digest of a leaf is visible, and the secret tail of a leaf's answer has 0 bits. So a program
gets a leaf's digest as a value at once; the inner nodes of a tree are ordinary queries on values;
the roots are values in a Fiat-Shamir query; and hashing needs no reveal. The tail of 0 bits is
still a token: it is shown together with the leaf's salt when the leaf is opened, as the rules ask
(a released evaluation has its tail shown).

Main names (namespace OnBytes.TokenSide).
  visT, tlT, splitT   the visible part, the length of the tail, the split.
  StT lam K L α       a token program over the second form's oracles with this split.
  digOf, valOf        a string as a digest; the value of a token, out of the list of tokens that a
                      reveal has named and the list of strings that it has returned.
  bitsT, digT, digsT  uniform bits, a uniform digest, a list of uniform digests, as values (not
                      tokens): for coins that no evaluation is charged to.
  plT, mkT, bitsOfT, rulesT   the rules.
  osT0, osT           the oracles with marked evaluations.

The rules. Ordinary queries: the inner nodes of trees; and, at a Fiat-Shamir oracle, the points of a
set sd that is a letter here (meant: the two queries from which a table's seed is read). Marked
evaluations: leaves, charged to the free bits of a salt (at least bl bits: the public start of a
salt is part of the point and is not counted); Fiat-Shamir queries and the later tries of a search
under the names fbw t k, charged to a chain's salt or to a chaining value, a slot value or a request
root (at least bf bits); g, and the leaf and the inner nodes of a request path, charged to strings
of lam bits.

Limits. Definitions. Nothing is said here on any program. bl and bf are letters: that a program's
tokens have these lengths is shown where the program is.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Compile.SpecDiscipline
import Iop.BatchWire

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type}

/-! ## The split -/

/-- the visible part of an answer -/
def visT (lam K : ℕ) : OracleName → Type
  | .leaf => Dig lam
  | .node => Dig lam
  | .rleaf => Unit
  | .rnode => Unit
  | .fb _ => Fin K → Dig lam
  | .fbw _ _ => Fin K → Dig lam
  | .g _ => Unit
  | .ann => Unit
  | .other => Dig lam

/-- the number of bits of the secret tail of an answer -/
def tlT (lam : ℕ) : OracleName → ℕ
  | .leaf => 0
  | .node => 0
  | .rleaf => lam
  | .rnode => lam
  | .fb _ => lam
  | .fbw _ _ => lam
  | .g _ => lam
  | .ann => 0
  | .other => 0

/-- **The split.** A leaf's digest is visible. Of a Fiat-Shamir answer the blocks are visible and
the chaining value is the tail. An answer of g, or of a request tree's oracles, is a tail as a
whole. -/
def splitT (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : Split (typedOracleFamily lam K L) where
  Vis := visT lam K
  tl := tlT lam
  split := fun o => match o with
    | .leaf => (Equiv.prodUnique (Dig lam) (Fin 0 → Bool)).symm
    | .node => (Equiv.prodUnique (Dig lam) (Fin 0 → Bool)).symm
    | .rleaf => (Equiv.punitProd (Dig lam)).symm
    | .rnode => (Equiv.punitProd (Dig lam)).symm
    | .fb _ => Equiv.refl _
    | .fbw _ _ => Equiv.refl _
    | .g _ => (Equiv.punitProd (Dig lam)).symm
    | .ann => (Equiv.prodUnique Unit (Fin 0 → Bool)).symm
    | .other => (Equiv.prodUnique (Dig lam) (Fin 0 → Bool)).symm

/-- a token program over the second form's oracles -/
abbrev StT (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (α : Type) : Type := Step (typedOracleFamily lam K L) (splitT lam K L) α

/-! ## Small tools -/

/-- a string as a digest: its first lam bits; false beyond its end -/
def digOf (lam : ℕ) (v : Bits) : Dig lam := fun i => v.getD i.val false

theorem digOf_ofFn (lam : ℕ) (c : Dig lam) : digOf lam (List.ofFn c) = c := by
  funext i
  simp [digOf, List.getD_eq_getElem?_getD]

/-- The value of the token u, out of the tokens that a reveal has named and the strings that it has
returned; the empty string for a token that was not named. -/
def valOf : List Tok → List Bits → Tok → Bits
  | t :: ts, v :: vs, u => if u = t then v else valOf ts vs u
  | _, _, _ => []

/-- A reveal returns the values of the tokens that it names: so valOf reads them back. -/
theorem valOf_map (f : Tok → Bits) : ∀ (ts : List Tok) (u : Tok), u ∈ ts →
    valOf ts (ts.map f) u = f u
  | t :: ts, u, h => by
    show (if u = t then f t else valOf ts (ts.map f) u) = f u
    by_cases e : u = t
    · rw [if_pos e, e]
    · rw [if_neg e]
      exact valOf_map f ts u ((List.mem_cons.mp h).resolve_left e)

variable {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- ℓ uniform bits, as a value -/
def bitsT (ℓ : ℕ) : StT lam K L Bits :=
  Step.sample (2 ^ ℓ - 1) fun r => Step.pure (List.ofFn fun i : Fin ℓ => r.val.testBit i)

/-- a uniform digest, as a value -/
def digT : StT lam K L (Dig lam) :=
  Step.sample (2 ^ lam - 1) fun r => Step.pure fun i : Fin lam => r.val.testBit i

/-- n uniform digests, as values -/
def digsT : ℕ → StT lam K L (List (Dig lam))
  | 0 => .pure []
  | n + 1 => (digT (K := K) (L := L)).bind fun d => (digsT n).bind fun ds => .pure (d :: ds)

/-! ## The rules -/

/-- the allowed ordinary queries: inner nodes of trees; at a Fiat-Shamir oracle the points of sd -/
def plT (sd : (t : Tag) → FbIn lam L t → Prop) : (o : OracleName) → domOf lam L o → Prop
  | .node, _ => True
  | .fb t, q => sd t q
  | _, _ => False

/-- the oracles at which a marked evaluation is allowed -/
def mkT : OracleName → Prop
  | .leaf => True
  | .rleaf => True
  | .rnode => True
  | .fb _ => True
  | .fbw _ _ => True
  | .g _ => True
  | _ => False

/-- the least length of a token that is charged at an oracle -/
def bitsOfT (lam bl bf : ℕ) : OracleName → ℕ
  | .leaf => bl
  | .fb _ => bf
  | .fbw _ _ => bf
  | .rleaf => lam
  | .rnode => lam
  | .g _ => lam
  | _ => 0

/-- **The rules** of the token programs of this folder. bl: the free bits of a leaf's salt; bf: the
bits of a token that a Fiat-Shamir query is charged to; sd: the ordinary queries that are allowed at
a Fiat-Shamir oracle. -/
def rulesT (K : ℕ) (L : BatchProtocolWithLeafBody I X) (lam bl bf : ℕ) (sd : (t : Tag) → FbIn lam L t → Prop) :
    Compile.Disc.Rules (typedOracleFamily lam K L) where
  Term := fun _ => False
  Pl := plT sd
  Mk := fun o _ => mkT o
  bits := bitsOfT lam bl bf

/-- the nine oracles with marked evaluations beside the names fbw t k -/
def osT0 : Finset OracleName :=
  {.leaf, .rleaf, .rnode, .fb Tag.test, .fb Tag.link, .fb Tag.onl,
   .g Tag.test, .g Tag.link, .g Tag.onl}

/-- the same with the names fbw t k, k < m -/
def osT (m : ℕ) : Finset OracleName :=
  osT0 ∪ ((Finset.range m).image (OracleName.fbw Tag.test) ∪ (Finset.range m).image (OracleName.fbw Tag.link) ∪
      (Finset.range m).image (OracleName.fbw Tag.onl))

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.digOf_ofFn
#print axioms OnBytes.TokenSide.valOf_map
