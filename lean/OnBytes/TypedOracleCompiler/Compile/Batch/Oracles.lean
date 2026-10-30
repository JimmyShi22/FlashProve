-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean: a form of Compile/Batch/Oracles.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

What differs in this file from Compile/Batch/Oracles.lean, comments apart: definitions: `annOf`,
`LeafIn`, `Head`, `FbIn`, `JoiningRoundQuery`; only here: `QueryLayout.dReq`. Every other declaration has that file's
text.

Where the head below says "A query holds at most one root and one plain part": here a query holds a
list of roots (`FbIn.rt : List (Dig lam)`). Where it says "a root only where that component has a
tree", "(but for the field `rt` of the root: a digest)" and "the field `rt`, the root of the tree
over" a component: here `rt` is the list of the roots of the component's trees, empty if it has
none. The format (F5) holds no external roots here. Into the input of `rleaf` the verifier writes
lam bits and, behind them, the proof string's `rsalt`. Where it says that Test and Link have local
rounds only: here they have annotations of their own (`annT`, `annL`); the theorem of soundness asks
that these be all local (SpecSoundG.lean). The oracles of the request trees, `rleaf` and `rnode`,
bear no tag: so request trees of different depths and of different protocols share them; each lane
of the analysis extracts at its one depth (`QueryLayout.dReq`), and the queries (G) and (F4) are tagged.

The rest of this head is the head of Compile/Batch/Oracles.lean, to be read with these changes; the
files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name,
this folder's.

Compile/Batch/Oracles.lean: the typed random oracles of the compiled scheme.

`typedOracleFamily lam K L` is the family of independent random oracles, one for each kind of query, over which
the compiled scheme for the record of protocols `L` (Test, Link, Batch: `BatchProtocol`,
Iop/Batch.lean) is defined and analysed. Digests have `lam` bits. The oracles are (`OracleName`):

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

Limits: one difference from the implementation lies in how these queries are written: every query
(F2) has the field `xl`, empty in all rounds but one, where the implementation writes no word of x
and only its flags bit (docs/format/README.md, 3.6). The late query holds the whole x, so the prompt
a second time, as the implementation's does (known, for its verifier, by reading its sources). Also
open on this point: who computes y. This file says nothing on the positions that are sampled before
y (on them: files that are not in this library).
What this file's comments say of "the implementation" need not hold of the released programs
(lean/LIMITS.md, L1).

-/
import OnBytes.TypedOracleCompiler.Iop.BatchWire
import Compile.Oracles

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

inductive OracleName | leaf | node | rleaf | rnode | fb (t : Tag) | g (t : Tag) | ann | other
  /-- An oracle of the analysis, which no algorithm of the scheme ever queries. In a round with
  proof-of-work bits (Iop/BatchWire.lean: GrW) the honest prover queries fb t once for each nonce
  that it uses. Its program in the language of Rom/Defer.lean writes attempt number k + 1 as a query
  to fbw t k, at the same input; the scheme is that program with fb t written back for fbw t k
  (realQ below). Why: the header of Compile/Batch/SpecGhost.lean. -/
  | fbw (t : Tag) (k : ℕ)
  deriving DecidableEq

variable {I X : Type}

def shapeOf (L : BatchProtocolWithLeafBody I X) : Tag → Shape
  | .test => L.offline.shape
  | .link => L.link.shape
  | .onl => L.onlineBatch.loc.shape

/-- Here: the annotation of a protocol, by its tag: Test's and Link's are the interface's `annT`,
`annL`. -/
def annOf (L : BatchProtocolWithLeafBody I X) : (t : Tag) → RoundSplits (shapeOf L t)
  | .test => L.annT
  | .link => L.annL
  | .onl => L.onlineBatch.ann

/-- Here: the depth of a request tree, by the protocol -/
def _root_.TypedOracleCompiler.Iop.QueryLayout.dReq {lam : ℕ} {L : BatchProtocolWithLeafBody I X} (W : QueryLayout lam L) : Tag → ℕ
  | .test => W.depthReqT
  | .link => W.depthReqL
  | .onl => W.depthReq

/-- the plain part of one component of the prover message of some round: α_0 (left) or α_j
(right) -/
def PlainPart : (s : Shape) → RoundSplits s → Type
  | [], _ => Empty
  | _ :: s, (a, A) => (a.P0 ⊕ a.Pj) ⊕ PlainPart s A

/-- the input of a leaf of a tree over oracles: a body (here: of the type that the interface names;
in the library: a symbol of an encoded index, or of a prover oracle with protocol and position, or
padding); and a salt -/
structure LeafIn (L : BatchProtocolWithLeafBody I X) where
  body : L.Bd
  salt : Bits

/-- The formats of a Fiat-Shamir query, without the root and the plain part, which all of them
have. -/
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
  /-- (F5): a later shared round: pp ‖ ρ_0 ‖ rt_0 ‖ α_0. It holds no outer root, as a shared round's
  hash call in the byte format as it ships holds none: outside the event E_F the chain value ρ_0
  leads back to (F4), which holds them. -/
  | f5 (ρ0 : Bits)

/-- What of the instance x the query of round i holds beside what is in (F1): x itself in the round
L.late, nothing elsewhere. -/
def lateInstancePart (L : BatchProtocolWithLeafBody I X) (i : ℕ) (x : Option X) : Option X := if L.late = some i then x else none

/-- the header with the field xl, if its format has that field -/
def Head.withLate {lam : ℕ} : Head lam X → Option X → Head lam X
  | .f2 _ ρ, xl => .f2 xl ρ
  | h, _ => h

/-- the field xl of a header; none if its format has no such field -/
def Head.late {lam : ℕ} : Head lam X → Option X
  | .f2 xl _ => xl
  | _ => none

structure FbIn (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (t : Tag) where
  round : ℕ
  head : Head lam X
  /-- Here: the roots of the trees of the component, in the order of the wire; []: no tree -/
  rt : List (Dig lam)
  plain : PlainPart (shapeOf L t) (annOf L t)

/-- (G): ρ ‖ rt ‖ α, with the slot's message of the joining round -/
structure JoiningRoundQuery (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (t : Tag) where
  round : ℕ
  ρ : Bits
  rt : List (Dig lam)
  plain : PlainPart (shapeOf L t) (annOf L t)

def domOf (lam : ℕ) (L : BatchProtocolWithLeafBody I X) : OracleName → Type
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
def typedOracleFamily (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : OSpec where
  ι := OracleName
  Dom := domOf lam L
  Rng := rngOf lam K

/-- An algorithm with the analysis's oracles written back: a query to fbw t k becomes the query to
fb t at the same input. All else is unchanged. -/
def realQ {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {α : Type} : OComp (typedOracleFamily lam K L) α → OComp (typedOracleFamily lam K L) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => realQ (k r)
  | .query (.fbw t _) q k => .query (S := typedOracleFamily lam K L) (.fb t) q fun r => realQ (k r)
  | .query o q k => .query o q fun r => realQ (k r)

end TypedOracleCompiler.Compile.Batch
