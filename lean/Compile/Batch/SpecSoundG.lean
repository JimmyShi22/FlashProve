-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
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
import Compile.Batch.Events

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

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
-/
def Spec.bcsSoundBatchG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (Rno : I → X → Prop) (εs : ℝ≥0∞),
    L.Sound Rno εs → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKG → BcsAt W Rno εs

end Compile.Batch
