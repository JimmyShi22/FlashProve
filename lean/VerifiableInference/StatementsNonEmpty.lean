-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/StatementsNonEmpty.lean

The top statements of VerifiableInference/Statements.lean without the corner case of the empty list
of output tokens. ONE CONJUNCT DIFFERS, IN ONE DEFINITION, WHICH THAT FILE DOES NOT HOLD:
  `IsModelOutputNonEmpty` := `output ≠ []` and `IsModelOutput`.
Each of the six statements here is the statement there with `IsModelOutputNonEmpty` in the place of
`IsModelOutput`, and every other token the same.

The corner case. The empty list of output tokens is the model's on every prompt, at all weights:
"each of them is the model's next token" asks nothing of no token (`isModelOutput_nil`). So:
  `Sound`, `SoundAndBinding`, `SoundOpened` are silent on it: a verifier that accepts the empty list
    is not at fault there (in the first two: as soon as the extractor gives any weights).
    THE FORMS HERE ARE STRONGER: an accepted empty list counts as a failure
    (`sound_of_soundNonEmpty` and its like: each form here gives the form there).
  `Complete` asks that an honest proof of nothing is accepted: a verifier that refuses a request
    without output tokens is not complete, at any error below 1, for that reason alone.
    THE FORM HERE ASKS LESS: the requests that have an output token (`completeNonEmpty_of_complete`;
    it is `CompleteOn` on these: `completeNonEmpty_iff_completeOn`).
  `ZeroKnowledge` lets the verifier ask for proofs of nothing. THE FORM HERE ASKS LESS
    (`zeroKnowledgeNonEmpty_of_zeroKnowledge`; it is `ZeroKnowledgeOn` on these requests).
  `CompleteSoundZeroKnowledge`: its three fields are replaced by their forms here. Neither bundle
    gives the other.

What this file does not do. It takes out the empty list and nothing else. Whether a system's honest
prover can make a proof for every other request (a token outside the vocabulary; a value that leaves
a table's range) is another matter: see `CompleteOn` (VerifiableInference/Steps.lean) and `CanServe`
(VerifiableInference/CanServe.lean).

-/
import VerifiableInference.Statements
import VerifiableInference.Steps
import VerifiableInference.MoreStatements

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference

/-! ## 1. The one new conjunct -/

/-- The output tokens are the model's, and there is one: `IsModelOutput` with `output ≠ []`. -/
def ArgumentSystem.IsModelOutputNonEmpty (system : ArgumentSystem) (weights : system.Weights)
    (prompt output : List Token) : Prop :=
  output ≠ [] ∧ system.IsModelOutput weights prompt output

/-- The empty list of output tokens is the model's, on every prompt and at all weights. -/
theorem isModelOutput_nil (system : ArgumentSystem) (weights : system.Weights)
    (prompt : List Token) : system.IsModelOutput weights prompt [] :=
  fun _ h => absurd h (Nat.not_lt_zero _)

/-- With the new conjunct it is not. -/
theorem not_isModelOutputNonEmpty_nil (system : ArgumentSystem) (weights : system.Weights)
    (prompt : List Token) : ¬ system.IsModelOutputNonEmpty weights prompt [] :=
  fun h => h.1 rfl

/-! ## 2. The six statements -/

/-- `Sound` with `IsModelOutputNonEmpty` in the place of `IsModelOutput`. -/
def SoundNonEmpty (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (extractor commitment queryLog, prompt, output, accepted))
          {(extracted, prompt, output, accepted) |
            accepted = true ∧
            ¬ ∃ weights, extracted = some weights ∧
              system.IsModelOutputNonEmpty weights prompt output}
          ≤ ε (committerQueries + proverQueries)

/-- `SoundAndBinding` with `IsModelOutputNonEmpty` in the place of `IsModelOutput`. -/
def SoundAndBindingNonEmpty (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      (∀ prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (extractor commitment queryLog, prompt, output, accepted))
          {(extracted, prompt, output, accepted) |
            accepted = true ∧
            ¬ ∃ weights, extracted = some weights ∧
              system.IsModelOutputNonEmpty weights prompt output}
          ≤ ε (committerQueries + proverQueries)) ∧
      (∀ opener : State → RandomizedAlgorithm (system.Weights × system.CommitmentRandomness),
        (∀ state, (opener state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (weights, randomness) ← opener state
            let recomputed ← (system.commit weights randomness).toRandomized
            pure (extractor commitment queryLog, commitment, weights, recomputed))
          {(extracted, commitment, weights, recomputed) |
            recomputed = commitment ∧ extracted ≠ some weights}
          ≤ ε (committerQueries + proverQueries))

/-- `SoundOpened` with `IsModelOutputNonEmpty` in the place of `IsModelOutput`. -/
def SoundOpenedNonEmpty (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (queries : ℕ)
    (adversary : RandomizedAlgorithm
      (Commitment × (system.Weights × system.CommitmentRandomness) ×
          (List Token × List Token × system.Proof))),
    adversary.QueryBound queries →
      Prob (do
          let (commitment, (weights, randomness), (prompt, output, proof)) ← adversary
          let recomputed ← (system.commit weights randomness).toRandomized
          let accepted ← (system.verify commitment prompt output proof).toRandomized
          pure (commitment, recomputed, weights, prompt, output, accepted))
        {(commitment, recomputed, weights, prompt, output, accepted) |
          recomputed = commitment ∧ accepted = true ∧
            ¬ system.IsModelOutputNonEmpty weights prompt output}
        ≤ ε queries

/-- `Complete` with `IsModelOutputNonEmpty` in the place of `IsModelOutput`. -/
def CompleteNonEmpty (system : ArgumentSystem) (α : ℝ≥0∞) : Prop :=
  ∀ (weights : system.Weights) (prompt output : List Token),
    system.IsModelOutputNonEmpty weights prompt output →
      Prob (do
          let randomness ← system.sampleCommitmentRandomness
          let commitment ← (system.commit weights randomness).toRandomized
          let proof ← system.prove weights randomness prompt output
          (system.verify commitment prompt output proof).toRandomized)
        {accepted | accepted = false}
        ≤ α

/-- `ZeroKnowledge` with `IsModelOutputNonEmpty` in the place of `IsModelOutput`. -/
def ZeroKnowledgeNonEmpty (system : ArgumentSystem) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ simulator : Simulator system.PublicParameters system.Proof,
    ∀ (weights : system.Weights)
      (chooser : View system.Proof → Option (List Token × List Token)),
      (∀ view prompt output, chooser view = some (prompt, output) →
          system.IsModelOutputNonEmpty weights prompt output) →
      ∀ (queries : ℕ) (verifier : Commitment → MaliciousVerifier system.Proof) (proofCount : ℕ),
        (∀ commitment, (verifier commitment).QueryBound queries) →
          statisticalDistance
              (Prob (realExperiment system verifier chooser weights proofCount))
              (eventProbability (simulatedExperiment system simulator verifier chooser weights
                  proofCount))
            ≤ ζ queries proofCount
          ∧ eventProbability (simulatedExperiment system simulator verifier chooser weights
              proofCount)
              {view | ¬ view.queryLog.Consistent} = 0

/-- `CompleteSoundZeroKnowledge` with the three forms of this file. -/
structure CompleteSoundZeroKnowledgeNonEmpty (system : ArgumentSystem) (α : ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  sound : SoundNonEmpty system ε
  complete : CompleteNonEmpty system α
  zeroKnowledge : ZeroKnowledgeNonEmpty system ζ

/-! ## 3. How they stand to the statements of Statements.lean -/

/-- A larger event is at least as likely. -/
theorem Prob_mono {α : Type} (experiment : RandomizedAlgorithm α) {S T : Set α} (h : S ⊆ T) :
    Prob experiment S ≤ Prob experiment T := by
  unfold Prob eventProbability
  exact MeasureTheory.lintegral_mono fun hash => (experiment.run hash).toOuterMeasure.mono h

/-- **`SoundNonEmpty` gives `Sound`.** -/
theorem sound_of_soundNonEmpty {system : ArgumentSystem} {ε : ℕ → ℝ≥0∞}
    (h : SoundNonEmpty system ε) : Sound system ε := by
  obtain ⟨extractor, h⟩ := h
  refine ⟨extractor, fun cq pq State committer hc prover hp => ?_⟩
  refine le_trans (Prob_mono _ ?_) (h cq pq State committer hc prover hp)
  rintro ⟨extracted, prompt, output, accepted⟩ ⟨ha, hn⟩
  exact ⟨ha, fun ⟨w, hw, ho⟩ => hn ⟨w, hw, ho.2⟩⟩

/-- **`SoundAndBindingNonEmpty` gives `SoundAndBinding`.** -/
theorem soundAndBinding_of_soundAndBindingNonEmpty {system : ArgumentSystem} {ε : ℕ → ℝ≥0∞}
    (h : SoundAndBindingNonEmpty system ε) : SoundAndBinding system ε := by
  obtain ⟨extractor, h⟩ := h
  refine ⟨extractor, fun cq pq State committer hc => ⟨fun prover hp => ?_,
    (h cq pq State committer hc).2⟩⟩
  refine le_trans (Prob_mono _ ?_) ((h cq pq State committer hc).1 prover hp)
  rintro ⟨extracted, prompt, output, accepted⟩ ⟨ha, hn⟩
  exact ⟨ha, fun ⟨w, hw, ho⟩ => hn ⟨w, hw, ho.2⟩⟩

/-- **`SoundOpenedNonEmpty` gives `SoundOpened`.** -/
theorem soundOpened_of_soundOpenedNonEmpty {system : ArgumentSystem} {ε : ℕ → ℝ≥0∞}
    (h : SoundOpenedNonEmpty system ε) : SoundOpened system ε := by
  intro queries adversary ha
  refine le_trans (Prob_mono _ ?_) (h queries adversary ha)
  rintro ⟨commitment, recomputed, weights, prompt, output, accepted⟩ ⟨h1, h2, h3⟩
  exact ⟨h1, h2, fun ho => h3 ho.2⟩

/-- `SoundNonEmpty` is soundness for the claim "the output tokens are the model's, and there is
one". -/
theorem soundNonEmpty_iff_soundFor (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) :
    SoundNonEmpty system ε ↔ SoundFor system system.IsModelOutputNonEmpty ε := Iff.rfl

/-- **`Complete` gives `CompleteNonEmpty`.** -/
theorem completeNonEmpty_of_complete {system : ArgumentSystem} {α : ℝ≥0∞}
    (h : Complete system α) : CompleteNonEmpty system α :=
  fun weights prompt output hOutput => h weights prompt output hOutput.2

/-- `CompleteNonEmpty` is `CompleteOn` on the requests that have an output token. -/
theorem completeNonEmpty_iff_completeOn (system : ArgumentSystem) (α : ℝ≥0∞) :
    CompleteNonEmpty system α ↔ CompleteOn system (fun _ _ output => output ≠ []) α :=
  ⟨fun h weights prompt output h1 h2 => h weights prompt output ⟨h1, h2⟩,
   fun h weights prompt output h12 => h weights prompt output h12.1 h12.2⟩

/-- `ZeroKnowledgeNonEmpty` is `ZeroKnowledgeOn` on the requests that have an output token. -/
theorem zeroKnowledgeNonEmpty_iff_zeroKnowledgeOn (system : ArgumentSystem) (ζ : ℕ → ℕ → ℝ≥0∞) :
    ZeroKnowledgeNonEmpty system ζ ↔ ZeroKnowledgeOn system (fun _ _ output => output ≠ []) ζ :=
  Iff.rfl

/-- **`ZeroKnowledge` gives `ZeroKnowledgeNonEmpty`.** -/
theorem zeroKnowledgeNonEmpty_of_zeroKnowledge {system : ArgumentSystem} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : ZeroKnowledge system ζ) : ZeroKnowledgeNonEmpty system ζ := by
  obtain ⟨simulator, h⟩ := h
  exact ⟨simulator, fun weights chooser hc =>
    h weights chooser fun view prompt output hv => (hc view prompt output hv).2⟩

end VerifiableInference

#print axioms VerifiableInference.sound_of_soundNonEmpty
#print axioms VerifiableInference.soundAndBinding_of_soundAndBindingNonEmpty
#print axioms VerifiableInference.soundOpened_of_soundOpenedNonEmpty
#print axioms VerifiableInference.completeNonEmpty_of_complete
#print axioms VerifiableInference.completeNonEmpty_iff_completeOn
#print axioms VerifiableInference.zeroKnowledgeNonEmpty_iff_zeroKnowledgeOn
#print axioms VerifiableInference.zeroKnowledgeNonEmpty_of_zeroKnowledge
