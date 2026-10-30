-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowSoundSpec.lean: BCS with shared rounds, many proofs, with a witness.

This file is about soundness of an interactive oracle proof compiled with Merkle trees and
Fiat-Shamir queries (BCS), with a witness: under the hypotheses of `Spec.bcsSoundBatchK`, outside an
event Bad on lists of queries, a proof that the compiled verifier of a slot of Batch accepts, with
all its queries in the list, yields oracles off which a witness is read, unless the encoded index
does not decode.
A definition and a statement. The proof: CompileK/KnowSound.lean. The three protocols are those of
the interface: Test (`L.offline`), Link (`L.link`) and Batch (`L.onlineBatch`).

Main names:
  `BcsAtK W Rno wit εs`: `BcsAt` of Compile/Batch/SpecSoundG.lean with two changes. Its clauses 1 to
    4 and 6 are those of `BcsAt`, word for word: there is an event Bad on traces that is rare for
    every t-query algorithm (the same bound), is never undone, outside which an accepted proof of
    Test or Link has its statement in the language, and outside which what is extracted under an
    announced root never changes.
    Changed, the clause for a slot of Batch: outside Bad, if the compiled verifier of a slot accepts
    (x, π) and all its queries are in the trace, then the encoded index under the root does not
    decode, or it decodes to an index i and the named value wit x (readB W tr π) is a witness of
    `(i, x)`. `readB W tr π` (CompileK/KnowExt.lean) reads the roots off π and the trees off the
    trace; no verifier message, bound by no "there is".
    New, the last clause: outside Bad, what `readB` reads does not change when the trace goes on,
    once all roots of π that belong to a round occur in it.
  `Spec.bcsSoundBatchK`: round-by-round knowledge soundness of the interface (`Iop.BatchProtocol.SoundK`,
    Hiop/Interface.lean), locality of the three verifiers, coherence of the annotation and the laws
    of the wire (`W.OKG`) give `BcsAtK`.

Limits: this file says nothing about the experiment that defines index binding: there the extractor
is given the committer's and the prover's trace, not the verifier's (CompileK/KnowBinding.lean
closes that gap with the last clause). It says nothing about which εs an interface has. At a bound
of 1 or more the first clause is empty, as in `BcsAt`.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowStarDefs
import Hiop.Interface

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The conclusion of BCS with shared rounds, with the named witness, for one wire. -/
def BcsAtK (W : QueryLayout lam L) (Rno : I → X → Wn → Prop)
    (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cm π, ¬ Bad tr → RunsIn tr (vT W cm π) true → L.decodeIndex (extEnc W tr cm) ≠ none) ∧
    (∀ tr cm cm' π, ¬ Bad tr → RunsIn tr (vL W cm cm' π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ L.decodeIndex (extEnc W tr cm') = L.decodeIndex (extEnc W tr cm)) ∧
    (∀ tr cm x π, ¬ Bad tr → RunsIn tr (vB W cm x π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) = some i ∧ Rno i x (wit x (readB W tr π))) ∧
    (∀ tr tr' cm,
      ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm) ∧
    (∀ tr tr' π, ¬ Bad (tr ++ tr') → (∀ c ∈ RootsOfChain.list L.onlineBatch.loc.shape (rtsB W π), (evM lam W.K L).OccursIn tr c) →
      readB W tr π = readB W (tr ++ tr') π)

/-- BCS with shared rounds, many proofs, with a witness, for a wire whose rounds may have proof of
work. -/
def Spec.bcsSoundBatchK : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    L.SoundK Rno wit εs → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal → L.onlineBatch.ann.Coherent →
    W.OKG → BcsAtK W Rno wit εs

end Compile.Batch
