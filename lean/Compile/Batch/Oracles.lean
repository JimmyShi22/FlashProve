-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Oracles.lean: the typed random oracles of the compiled scheme.

`spec lam K L` is the family of independent random oracles, one for each kind of query, over which
the compiled scheme for the record of protocols `L` (Test, Link, Batch: `BatchProtocol`, Iop/Batch.lean) is
defined and analysed. Digests have `lam` bits. The oracles are (`OracleName`):

  `leaf`, `node`    the Merkle trees over prover messages and over encodings of the index;
  `rleaf`, `rnode`  the request tree, a Merkle tree over the slots of one batch;
  `fb t`            Fiat-Shamir for the protocol t, with the round as a field of the query; an
                    answer is K hash blocks, from which the challenge is made, and a chaining value;
  `g t`             in the joining round (the first shared round after the local ones), the slot
                    value: the hash of a slot's chain that becomes its leaf in the request tree;
  `ann`             a trivial answer: a query to it announces a digest, for the analysis;
  `other`           the auxiliary oracle on bit strings, which only the schemes with a seed query,
                    to derive coins;
  `fbw t k`         the analysis's oracles, never queried by the scheme: proof-of-work attempt k + 1
                    is written as a query to `fbw t k`, and `realQ` maps it back to `fb t`.

A Fiat-Shamir query (`FbIn`) has one of the five formats (F1) to (F5) (`Head`), by the place of its
round among local and shared rounds; (G) is the format of a query to g. (T1) is (F1) and (T2) is
(F2): Test and Link have local rounds only. A query holds at most one root and one plain part (what
a prover message sends in the clear, not as an oracle), of the slot's or of the shared component of
the message, and a root only where that component has a tree, as in the implementation. The public
parameters are fixed and are not a field. Fields for strings that the honest prover keeps secret for
a while have the type of all bit strings (but for the field `rt` of the root: a digest), as
Rom/Defer.lean needs.

The instance may enter a chain in two parts: (F1) holds `L.early x`, and the query (F2) of the round
`L.late` holds x (`lateInstancePart`). The implementation writes a request's answer y into its chain only at
the start of the last sub-proof, because the prover computes y there.

Notation:
  the letters of the formats at `Head` and `JoiningRoundQuery`:
  cm..: the field `cms`: the roots of the trees over the external strings (`chainsU`,
    Compile/Batch/SeedLazyDefs.lean)
  rt, rt_0: the field `rt`, the root of the tree over the slot's, and over the shared, component; α,
    α_j, α_0: the field `plain`, the plain part of that component (`PlainPart`)
  ρ, ρ_0: the previous chaining value; in (F3) ρ_0 is the last shared chaining value and c the slot
    value; rt_req: the request root (the head of Compile/Batch/Prover.lean)

Limits: one difference from the implementation in how these queries are written: every query
(F2) has the field `xl`, empty in all rounds but one, where the implementation writes no word of x
and only its flags bit (docs/format/README.md, 3.6). The late query holds the whole x, so the prompt
a second time, as the implementation's does (known, for its verifier, by reading its sources). This
file does not fix who computes y, and says nothing on the positions that are sampled before
y (on them: files that are not in this library).
A query (F5) holds no external roots.

This file does not compare the implementation on this point.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Iop.BatchWire
import Compile.Oracles

namespace Compile.Batch
open Iop Rom

inductive OracleName | leaf | node | rleaf | rnode | fb (t : Tag) | g (t : Tag) | ann | other
  /-- An oracle of the analysis, which no algorithm of the scheme ever queries. In a round with
  proof-of-work bits (Iop/BatchWire.lean: GrW) the honest prover queries fb t once for each nonce
  that it uses. Its program in the language of Rom/Defer.lean writes attempt number k + 1 as a query
  to fbw t k, at the same input; the scheme is that program with fb t written back for fbw t k
  (realQ below). Why: the header of Compile/Batch/SpecGhost.lean. -/
  | fbw (t : Tag) (k : ℕ)
  deriving DecidableEq

variable {I X : Type}

def shapeOf (L : BatchProtocol I X) : Tag → Shape
  | .test => L.offline.shape
  | .link => L.link.shape
  | .onl => L.onlineBatch.loc.shape

/-- Test and Link have local rounds only. -/
def annOf (L : BatchProtocol I X) : (t : Tag) → RoundSplits (shapeOf L t)
  | .test => RoundSplits.allLocal L.offline.shape
  | .link => RoundSplits.allLocal L.link.shape
  | .onl => L.onlineBatch.ann

/-- the plain part of one component of the prover message of some round: α_0 (left) or α_j
(right) -/
def PlainPart : (s : Shape) → RoundSplits s → Type
  | [], _ => Empty
  | _ :: s, (a, A) => (a.P0 ⊕ a.Pj) ⊕ PlainPart s A

/-- the input of a leaf of a tree over oracles: a symbol of an encoded index, or of a prover oracle
(with protocol and position), or padding; and a salt -/
structure LeafIn (L : BatchProtocol I X) where
  body : Option (L.Symbol ⊕ (Σ t : Tag, SymAny (shapeOf L t)))
  salt : Bits

/-- The formats of a Fiat-Shamir query, without the root and the plain part, which all of them
have. Where a format below is written with pp, the constructor has no field for it. -/
inductive Head (lam : ℕ) (X : Type)
  /-- (F1), (T1): the first query of a chain: pp ‖ cm.. ‖ x ‖ rt ‖ α ‖ salt (the scheme writes
  L.early x in the place of x) -/
  | f1 (cms : List (Dig lam)) (x : Option X) (salt : Bits)
  /-- (F2), (T2): this round and the one before are local: ρ ‖ rt ‖ α; and a field xl: the whole
  instance in the round L.late, nothing in every other round -/
  | f2 (xl : Option X) (ρ : Bits)
  /-- (F3): the first local round after the shared rounds: ρ_0 ‖ c ‖ rt ‖ α -/
  | f3 (ρ0 : Bits) (c : Bits)
  /-- (F4): the joining round: pp ‖ cm ‖ rt_req ‖ rt_0 ‖ α_0 -/
  | f4 (cms : List (Dig lam)) (rtreq : Bits)
  /-- (F5): a later shared round: ρ_0 ‖ rt_0 ‖ α_0. It holds no external roots: the chaining value
  ρ_0 leads back to (F4), which holds them. -/
  | f5 (ρ0 : Bits)

/-- What of the instance x the query of round i holds beside what is in (F1): x itself in the round
L.late, nothing elsewhere. -/
def lateInstancePart (L : BatchProtocol I X) (i : ℕ) (x : Option X) : Option X := if L.late = some i then x else none

/-- the header with the field xl, if its format has that field -/
def Head.withLate {lam : ℕ} : Head lam X → Option X → Head lam X
  | .f2 _ ρ, xl => .f2 xl ρ
  | h, _ => h

/-- the field xl of a header; none if its format has no such field -/
def Head.late {lam : ℕ} : Head lam X → Option X
  | .f2 xl _ => xl
  | _ => none

structure FbIn (lam : ℕ) (L : BatchProtocol I X) (t : Tag) where
  round : ℕ
  head : Head lam X
  rt : Option (Dig lam)
  plain : PlainPart (shapeOf L t) (annOf L t)

/-- (G): ρ ‖ rt ‖ α, with the slot's message of the joining round -/
structure JoiningRoundQuery (lam : ℕ) (L : BatchProtocol I X) (t : Tag) where
  round : ℕ
  ρ : Bits
  rt : Option (Dig lam)
  plain : PlainPart (shapeOf L t) (annOf L t)

def domOf (lam : ℕ) (L : BatchProtocol I X) : OracleName → Type
  | .leaf => LeafIn L
  | .node => Bits × Bits
  | .rleaf => Bits
  | .rnode => Bits × Bits
  | .fb t => FbIn lam L t
  | .fbw t _ => FbIn lam L t
  | .g t => JoiningRoundQuery lam L t
  | .ann => Dig lam
  | .other => List Bool
def rngOf (lam K : ℕ) : OracleName → Type
  | .leaf => Dig lam
  | .node => Dig lam
  | .rleaf => Dig lam
  | .rnode => Dig lam
  | .fb _ => (Fin K → Dig lam) × Dig lam
  | .fbw _ _ => (Fin K → Dig lam) × Dig lam
  | .g _ => Dig lam
  | .ann => Unit
  | .other => Dig lam

instance (lam K : ℕ) : ∀ o, Fintype (rngOf lam K o)
  | .leaf => inferInstanceAs (Fintype (Dig lam))
  | .node => inferInstanceAs (Fintype (Dig lam))
  | .rleaf => inferInstanceAs (Fintype (Dig lam))
  | .rnode => inferInstanceAs (Fintype (Dig lam))
  | .fb _ => inferInstanceAs (Fintype ((Fin K → Dig lam) × Dig lam))
  | .fbw _ _ => inferInstanceAs (Fintype ((Fin K → Dig lam) × Dig lam))
  | .g _ => inferInstanceAs (Fintype (Dig lam))
  | .ann => inferInstanceAs (Fintype Unit)
  | .other => inferInstanceAs (Fintype (Dig lam))
instance (lam K : ℕ) : ∀ o, Nonempty (rngOf lam K o)
  | .leaf => inferInstanceAs (Nonempty (Dig lam))
  | .node => inferInstanceAs (Nonempty (Dig lam))
  | .rleaf => inferInstanceAs (Nonempty (Dig lam))
  | .rnode => inferInstanceAs (Nonempty (Dig lam))
  | .fb _ => inferInstanceAs (Nonempty ((Fin K → Dig lam) × Dig lam))
  | .fbw _ _ => inferInstanceAs (Nonempty ((Fin K → Dig lam) × Dig lam))
  | .g _ => inferInstanceAs (Nonempty (Dig lam))
  | .ann => inferInstanceAs (Nonempty Unit)
  | .other => inferInstanceAs (Nonempty (Dig lam))

/-- The family of oracles. -/
def spec (lam K : ℕ) (L : BatchProtocol I X) : OSpec where
  ι := OracleName
  Dom := domOf lam L
  Rng := rngOf lam K

/-- An algorithm with the analysis's oracles written back: a query to fbw t k becomes the query to
fb t at the same input. All else is unchanged. -/
def realQ {lam K : ℕ} {L : BatchProtocol I X} {α : Type} : OComp (spec lam K L) α → OComp (spec lam K L) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => realQ (k r)
  | .query (.fbw t _) q k => .query (S := spec lam K L) (.fb t) q fun r => realQ (k r)
  | .query o q k => .query o q fun r => realQ (k r)

end Compile.Batch
