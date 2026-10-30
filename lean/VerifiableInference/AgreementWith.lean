-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/AgreementWith.lean

From properties of ZKCP/Defs.lean and ZKCP/Optional.lean to statements of this folder, for every
argument system, with the extractor named.
VerifiableInference/Agreement.lean proves that `Sound` and `Complete` agree with the library's index
binding and completeness. Proved here, the first three for the three algorithms
`system.uploadArgument` of an argument system:
  * `soundForWith_of_indexBindingWith`: index binding with a named extractor
    (ZKCP.HasIndexBindingWith), for a relation that implies a claim, gives soundness for that claim
    with the first part of that extractor (`SoundForWith`, VerifiableInference/MoreStatements.lean);
  * `completeOn_of_completenessError`: completeness error α (ZKCP.HasCompletenessError), for a
    relation that holds on a set of instances, gives completeness on that set (`CompleteOn`,
    VerifiableInference/Steps.lean);
  * `extracts_of_extractionError`: ZKCP.HasExtractionError gives `ExtractsCommittedWeights`
    (VerifiableInference/MoreStatements.lean) for the first part of the extractor;
  * `SoundForWith.soundAfterHonestCommitmentFor`: soundness for a claim and
    `ExtractsCommittedWeights`, for one extractor, give `SoundAfterHonestCommitmentFor`
    (VerifiableInference/MoreStatements.lean).
The extractor is `E.Ei`, the first part of the extractor E of ZKCP/Defs.lean. No bound grows, but:
soundness takes a bound in tC + tP that is at least the bound ε₂ of index binding in tC and tP, and
soundness after an honest commitment adds two bounds. A bound that is 1 or more says nothing.
The file is about no particular argument system.
-/
import VerifiableInference.AgreementZeroKnowledge
import VerifiableInference.MoreStatements
import VerifiableInference.Steps
import VerifiableInference.HonestCommitment
import ZKCP.Optional

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

variable (system : ArgumentSystem)

/-! ## 1. Soundness for a claim, with the extractor named -/

/-- Index binding with a named extractor gives soundness for a claim with that extractor. Let R be a
relation on weights and pairs of a prompt and output tokens, without witnesses, and let every pair
that is in R at given weights meet `claim` at these weights. If the algorithms of the argument
system have index binding for R with the extractor E and the bound ε₂ (ZKCP/Defs.lean:
HasIndexBindingWith), and ε₂ tC tP is at most ε (tC + tP), then soundness for `claim` holds with the
extractor `E.Ei` and the bound ε. -/
theorem soundForWith_of_indexBindingWith {PP : Type}
    (R : ZKCP.IndexedRelation system.Weights (List Token × List Token) Unit PP)
    (claim : system.Weights → List Token → List Token → Prop)
    (hR : ∀ (weights : system.Weights) (x : List Token × List Token), R.rel weights x () →
      claim weights x.1 x.2)
    (E : ZKCP.Extractor 256 system.Weights (List Token × List Token) Unit Commitment system.Proof)
    (ε₂ : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞) (hE : ZKCP.HasIndexBindingWith R system.uploadArgument E ε₂)
    (hε : ∀ tC tP, ε₂ tC tP ≤ ε (tC + tP)) : SoundForWith system E.Ei claim ε := by
  classical
  intro tC tP St committer hC prover hP
  have b1 := hE tC tP St committer.toUpload
    (fun state => ((prover state).bind fun y => RandomizedAlgorithm.done
        ((y.1, y.2.1), y.2.2)).toUpload)
    ((queryBound_toUpload committer tC).mpr hC)
    (fun state => (queryBound_toUpload _ tP).mpr (queryBound_map _ (prover state) tP (hP state)))
  refine le_trans ?_ (le_trans b1 (hε tC tP))
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  refine lintegral_mono fun H => ?_
  have e1 : (committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (E.Ei c.1.1 c.2, y.1, y.2.1, accepted)).run H
      = (committer.withQueryLog.run H).bind fun c =>
          (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
              ((y.1, y.2.1), y.2.2)).withQueryLog.run H).bind fun p =>
            PMF.pure (E.Ei c.1.1 c.2, p.1.1.1, p.1.1.2, (system.verify c.1.1 p.1.1.1 p.1.1.2
                p.1.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done]
    refine congrArg _ (funext fun c => ?_)
    rw [run_withQueryLog_bind_fst H ((prover c.1.2).bind fun y => RandomizedAlgorithm.done
        ((y.1, y.2.1), y.2.2))
      (fun x => PMF.pure (E.Ei c.1.1 c.2, x.1.1, x.1.2, (system.verify c.1.1 x.1.1 x.1.2
          x.2).evaluate H))]
    simp only [run_bind, run_done, PMF.bind_bind, PMF.pure_bind]
  have e2 : (committer.toUpload.withTrace.bind fun c =>
        (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
            ((y.1, y.2.1), y.2.2)).toUpload).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, E.Ei c.1.1 c.2, p.1.1, E.Ew c.1.1 c.2 p.1.1 p.1.2 p.2⟩ :
            ZKCP.BindingOutcome system.Weights (List Token × List Token) Unit)).run H
      = (committer.withQueryLog.run H).bind fun c =>
          (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
              ((y.1, y.2.1), y.2.2)).withQueryLog.run H).bind fun p =>
            PMF.pure ⟨(system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H, E.Ei c.1.1 c.2, p.1.1,
                ()⟩ := by
    simp only [ZKCP.run_bind, run_toUpload, run_toUpload_withTrace,
        DeterministicAlgorithm.run_toRandomized, PMF.pure_bind]
    rfl
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (E.Ei c.1.1 c.2, y.1, y.2.1, accepted)).run H) _
    ≤ ZKCP.prob ((committer.toUpload.withTrace.bind fun c =>
        (((prover c.1.2).bind fun y => RandomizedAlgorithm.done
            ((y.1, y.2.1), y.2.2)).toUpload).withTrace.bind fun p =>
        ((system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).toRandomized.toUpload).bind fun b =>
          ZKCP.OComp.pure (⟨b, E.Ei c.1.1 c.2, p.1.1, E.Ew c.1.1 c.2 p.1.1 p.1.2 p.2⟩ :
            ZKCP.BindingOutcome system.Weights (List Token × List Token) Unit)).run H) _
  rw [e1, e2, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun p => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le ?_
  rintro ⟨hAccepted, hBad⟩
  show (system.verify c.1.1 p.1.1.1 p.1.1.2 p.1.2).evaluate H = true ∧
    (p.1.1 ∉ R.L (E.Ei c.1.1 c.2) ∨ ¬ R.rel' (E.Ei c.1.1 c.2) p.1.1 ())
  refine ⟨hAccepted, ?_⟩
  cases hExtracted : E.Ei c.1.1 c.2 with
  | none => exact Or.inl (fun hx => hx)
  | some weights =>
      exact Or.inr (fun hRel => hBad ⟨weights, hExtracted, hR weights p.1.1 hRel⟩)

/-! ## 2. Completeness on a stated set of instances -/

/-- The experiment of `Complete` and `CompleteOn` is the library's completeness experiment
(ZKCP/Defs.lean: completenessExp): the two probabilities of rejection are equal. -/
theorem Prob_rejected_eq_Pr (weights : system.Weights) (prompt output : List Token) :
    Prob (do let randomness ← system.sampleCommitmentRandomness
             let commitment ← (system.commit weights randomness).toRandomized
             let proof ← system.prove weights randomness prompt output
             (system.verify commitment prompt output proof).toRandomized)
                 {accepted | accepted = false}
      = ZKCP.Pr (ZKCP.completenessExp system.uploadArgument weights (prompt, output) ())
          (fun _ => {b | b = false}) := by
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  refine lintegral_congr fun H => ?_
  show ZKCP.prob ((system.sampleCommitmentRandomness.bind fun randomness =>
        (system.commit weights randomness).toRandomized.bind fun commitment =>
        (system.prove weights randomness prompt output).bind fun proof =>
        (system.verify commitment prompt output proof).toRandomized).run H) _
    = ZKCP.prob (((system.committer weights).toUpload.bind fun k =>
        (system.prove k.2.1 k.2.2 prompt output).toUpload.bind fun π =>
        (system.verify k.1 prompt output π).toRandomized.toUpload).run H) _
  congr 1
  simp only [ZKCP.run_bind, run_toUpload, ArgumentSystem.committer, run_bind, run_done,
      PMF.bind_bind, PMF.pure_bind]

/-- Completeness error α gives completeness on a set of instances. Let R be a relation on weights
and pairs of a prompt and output tokens, without witnesses, that holds wherever `domain` holds and
the output tokens are the model's. If the algorithms of the argument system have completeness error
α for R (ZKCP/Defs.lean: HasCompletenessError), then `CompleteOn system domain α`. -/
theorem completeOn_of_completenessError {PP : Type}
    (R : ZKCP.IndexedRelation system.Weights (List Token × List Token) Unit PP)
    (domain : system.Weights → List Token → List Token → Prop)
    (hR : ∀ (weights : system.Weights) (prompt output : List Token), domain weights prompt output →
      system.IsModelOutput weights prompt output → R.rel weights (prompt, output) ())
    (α : ℝ≥0∞) (h : ZKCP.HasCompletenessError R system.uploadArgument α) :
    CompleteOn system domain α := by
  intro weights prompt output hDomain hOutput
  exact le_trans (le_of_eq (Prob_rejected_eq_Pr system weights prompt output))
    (h weights (prompt, output) () (hR weights prompt output hDomain hOutput))

/-! ## 3. From `HasExtractionError` to `ExtractsCommittedWeights` -/

/-- If the extractor E returns the honest committer's index except with probability δ
(ZKCP/Optional.lean: HasExtractionError, for the algorithms of the argument system), then `E.Ei`
gives back the honest committer's weights except with probability δ. -/
theorem extracts_of_extractionError
    (E : ZKCP.Extractor 256 system.Weights (List Token × List Token) Unit Commitment system.Proof)
    (δ : ℝ≥0∞) (h : ZKCP.HasExtractionError system.uploadArgument E δ) :
    ExtractsCommittedWeights system E.Ei δ := by
  intro weights
  refine le_trans (le_of_eq ?_) (h weights)
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  refine lintegral_congr fun hash => ?_
  show ZKCP.prob (((system.sampleCommitmentRandomness.bind fun randomness =>
        (system.commit weights randomness).toRandomized).withQueryLog.bind fun c =>
        RandomizedAlgorithm.done (E.Ei c.1 c.2)).run hash) {extracted | extracted ≠ some weights}
    = ZKCP.prob ((system.committer weights).toUpload.withTrace.run hash)
        {o | E.Ei o.1.1 o.2 ≠ some weights}
  have e : (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized).withQueryLog.run hash
      = ((system.committer weights).withQueryLog.run hash).bind fun out =>
          PMF.pure (out.1.1, out.2) :=
    run_withQueryLog_bind_map (fun (randomness : system.CommitmentRandomness)
        (commitment : Commitment) => (commitment, (weights, randomness)))
      Prod.fst (fun _ _ => rfl) (fun randomness => (system.commit weights randomness).toRandomized)
      hash system.sampleCommitmentRandomness
  rw [run_bind, e, PMF.bind_bind, run_toUpload_withTrace]
  simp only [PMF.pure_bind, run_done]
  exact prob_bind_pure_map _
    (fun out : (Commitment × (system.Weights × system.CommitmentRandomness)) × QueryLog =>
      E.Ei out.1.1 out.2) _

/-! ## 4. Soundness after an honest commitment -/

/-- Soundness for a claim, with an extractor that gives back the honest committer's weights except
with probability α, gives soundness after an honest commitment for that claim. The bound is
ε (committerQueries + proverQueries) + α: the honest committer's own queries count as if the prover
had made them. It is `SoundForWith.afterHonestCommitment`
(VerifiableInference/HonestCommitment.lean), stated with the definition. -/
theorem SoundForWith.soundAfterHonestCommitmentFor
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞) (α : ℝ≥0∞)
    (sound : SoundForWith system extractor claim ε)
    (extracts : ExtractsCommittedWeights system extractor α) :
    SoundAfterHonestCommitmentFor system claim
      fun committerQueries proverQueries => ε (committerQueries + proverQueries) + α :=
  fun weights committerQueries proverQueries committerBound prover proverBound =>
    SoundForWith.afterHonestCommitment system extractor claim ε α sound extracts weights
      committerQueries proverQueries committerBound prover proverBound

end VerifiableInference

#print axioms VerifiableInference.soundForWith_of_indexBindingWith
#print axioms VerifiableInference.Prob_rejected_eq_Pr
#print axioms VerifiableInference.completeOn_of_completenessError
#print axioms VerifiableInference.extracts_of_extractionError
#print axioms VerifiableInference.SoundForWith.soundAfterHonestCommitmentFor
