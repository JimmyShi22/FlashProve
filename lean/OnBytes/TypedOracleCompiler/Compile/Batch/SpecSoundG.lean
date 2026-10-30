-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/SpecSoundG.lean: a second form of Compile/Batch/SpecSoundG.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a second form of the verifier's side of
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

What differs in this file from Compile/Batch/SpecSoundG.lean, comments apart: definitions:
`Spec.bcsSoundBatchG`. Every other declaration has that file's text.

The theorem is for interfaces whose Test and Link have local rounds alone (its hypotheses `L.annT =
RoundSplits.allLocal L.offline.shape`, `L.annL = RoundSplits.allLocal L.link.shape`). So this end theorem does not
speak of a Test or Link with shared rounds, and so not of a key file of three joined chains; that
case rests on `mem_of_accepted`, `laneOf_ok` and `pr_stepS_le`, which do not ask that an annotation
be all local (`mem_of_accepted` asks that it be coherent, `laneOf_ok` the joint law at it); no
theorem of these files joins them for it. (lean/Johnson/TypedOracleCompiler/RecCompile/ does, for an object with
records: `cms_bcs`, CmsBcs.lean, and `cmsA_bcs`, CmsAns.lean, take any coherent annotations of Test
and Link.) The theorem has content only for wire records in which each component of a round has at
most `maxRt` = 2 Merkle trees; the laws of a wire record allow more; at such a record this verifier
rejects every string. A lawful wire of the library gives a lawful wire of this form, with at most
one tree a component (`ofB_okg`, OnBytes/TypedOracleCompiler/Tagged.lean); that a lawful wire of the library exists
is not shown in these files; that this verifier accepts any string is proved nowhere for this form.
Where the head below says that of the conditions on a round the proof uses only nine: here the proof
also uses the four laws of the wire on the bodies of leaves (`prjE_emb`, `prjT_emb`, `prjL_emb`,
`prjB_emb`).

The rest of this head is the head of Compile/Batch/SpecSoundG.lean, to be read with these changes;
the files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that
name, this folder's.

Compile/Batch/SpecSoundG.lean: BCS with shared rounds, many proofs, for a wire record whose rounds
may have proof-of-work bits. A definition and a statement. The proof: Compile/Batch/Sound.lean.

(Words of this library: lean/GLOSSARY.md.)

  `BcsAt`   the conclusion of Spec.bcsSoundBatch, a statement that is not in this library, for one
            wire record: there is an event Bad on traces that has probability at most t εs + 2 (t +
            1)² / 2^lam for every algorithm with at most t queries, is never undone, outside which
            every accepted compiled proof (accepted with the verifier's queries answered from the
            trace) has its statement in the language of its protocol with the extracted external
            strings, and outside which what is extracted under an announced root never changes
  `Spec.bcsSoundBatchG`   under `W.OKG` (Iop/BatchWire.lean: the conditions of `W.OK` on trees, leaf
                          numbers and verifier messages, without the condition that no round has
                          proof-of-work bits and with the condition that the proof-of-work records
                          are well formed, `GrW.OK`), `L.Sound Rno εs`, `IsLocal` for the three
                          verifiers, and `L.onlineBatch.ann.Coherent`: `BcsAt W Rno εs`

Why it is the same theorem as under `W.OK`. The verifier, the events and the extractor read nothing
of the proof-of-work records (`gr0`, `grJ`): of the scheme's algorithms only the honest prover (and
committer) reads these. In a record of protocols built by `L.grind` the verifier message holds the
proof-of-work bits and the interactive verifier rejects unless they are 0; εs bounds the round
errors of that record. So of the conditions on a round the proof uses only the nine that `WireRB.OK`
and `WireRB.OKG` share.

Limits: which εs a record of protocols with proof-of-work bits has is not said: that is a matter of
that record (Iop/BatchGrind.lean).

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Events

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the conclusion of Spec.bcsSoundBatch, a statement that is not in this library, for one wire
record (in words: the header) -/
def BcsAt (W : QueryLayout lam L) (Rno : I → X → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cm π, ¬ Bad tr → RunsIn tr (vT W cm π) true → L.decodeIndex (extEnc W tr cm) ≠ none) ∧
    (∀ tr cm cm' π, ¬ Bad tr → RunsIn tr (vL W cm cm' π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ L.decodeIndex (extEnc W tr cm') = L.decodeIndex (extEnc W tr cm)) ∧
    (∀ tr cm x π, ¬ Bad tr → RunsIn tr (vB W cm x π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) = some i ∧ Rno i x) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)

/-- BCS with shared rounds, many proofs, for a wire record whose rounds may have proof-of-work bits.
Here: under two hypotheses more: Test's and Link's annotations are all local (`L.annT =
RoundSplits.allLocal L.offline.shape`, `L.annL = RoundSplits.allLocal L.link.shape`). So this end theorem does not
speak of a Test or Link with shared rounds, and so not of a key file of three joined chains; that
case rests on `mem_of_accepted`, `laneOf_ok` and `pr_stepS_le`, which do not ask that an annotation
be all local (`mem_of_accepted` asks that it be coherent, `laneOf_ok` the joint law at it); no
theorem of these files joins them for it. (lean/Johnson/TypedOracleCompiler/RecCompile/ does, for an object with
records: `cms_bcs`, CmsBcs.lean, and `cmsA_bcs`, CmsAns.lean, take any coherent annotations of Test
and Link.) -/
def Spec.bcsSoundBatchG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (W : QueryLayout lam L) (Rno : I → X → Prop) (εs : ℝ≥0∞),
    L.Sound Rno εs → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKG → L.annT = RoundSplits.allLocal L.offline.shape →
    L.annL = RoundSplits.allLocal L.link.shape → BcsAt W Rno εs

end TypedOracleCompiler.Compile.Batch
