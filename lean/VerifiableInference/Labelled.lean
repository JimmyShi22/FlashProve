-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Labelled.lean: an argument system with a label beside each proof.

 1. labelled system label is system with a word beside each proof: its reply.
 2. The word is a function of the weights and the request: no coin, no hash query, no message.
 3. The prover of system runs at every request, and its proof goes out beside the word.
 4. The verifier is system's: it ignores the word. The committer, the weights and the model are too.
 5. The word is the honest side's, on the wire beside the proof. No verifier checks it.
 6. ZeroKnowledgeShownWhere is zero knowledge where the verifier is shown, beside each proof, what the
    simulator is told: they are one term, so what is shown is no more than what is declared.
 7. All its strength lies in which function is told: at the identity on the weights, a prover that
    sends the weights meets it.
 8. It follows from zero knowledge told the same function (zeroKnowledgeShown_of_told): it gives the
    honest view of a reply that carries the word.
-/
import VerifiableInference.AtEveryRequest

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference

/-- An argument system with a label beside each proof. -/
def labelled {Label : Type} (system : ArgumentSystem)
    (label : system.Weights → List Token × List Token → Label) : ArgumentSystem where
  Weights := system.Weights
  PublicParameters := system.PublicParameters
  publicParameters := system.publicParameters
  CommitmentRandomness := system.CommitmentRandomness
  Proof := Label × system.Proof
  nextToken := system.nextToken
  sampleCommitmentRandomness := system.sampleCommitmentRandomness
  commit := system.commit
  prove := fun weights randomness prompt output => do
    let proof ← system.prove weights randomness prompt output
    pure (label weights (prompt, output), proof)
  verify := fun commitment prompt output labelledProof =>
    system.verify commitment prompt output labelledProof.2

variable {Label : Type} (system : ArgumentSystem)
  (label : system.Weights → List Token × List Token → Label)

/-- The verifier of the labelled system is the system's, at the proof beside the word. -/
theorem labelled_verify (commitment : Commitment) (prompt output : List Token)
    (word : Label) (proof : system.Proof) :
    (labelled system label).verify commitment prompt output (word, proof) =
      system.verify commitment prompt output proof := rfl

/-- **The reply** at a request: the word, beside what the prover gives. -/
def reply (weights : system.Weights) (randomness : system.CommitmentRandomness)
    (prompt output : List Token) : RandomizedAlgorithm (Label × system.Proof) := do
  let proof ← system.prove weights randomness prompt output
  pure (label weights (prompt, output), proof)

/-- What the verifier is shown at a request is the reply at that request. -/
theorem shown_is_reply : (labelled system label).prove = reply system label := rfl

namespace AtEveryRequest

open scoped ENNReal

/-- **Zero knowledge, the verifier shown what the simulator is told.** The real side is the system's
own prover, run at every request that the chooser picks, with told's value beside each proof. All the
strength of this statement lies in which function told is. -/
def ZeroKnowledgeShownWhere {Told : Type} (system : ArgumentSystem) (hypothesis : Request → Prop)
    (told : system.Weights → Request → Told) (error : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ZeroKnowledgeWhere (labelled system told) hypothesis told error

/-- The same with a bar on the error: at most bar, up to queries hash queries and proofs proofs. -/
def ZeroKnowledgeShownBelowWhere {Told : Type} (system : ArgumentSystem)
    (hypothesis : Request → Prop) (told : system.Weights → Request → Told) (queries proofs : ℕ)
    (bar : ℝ≥0∞) : Prop :=
  ZeroKnowledgeBelowWhere (labelled system told) hypothesis told queries proofs bar

end AtEveryRequest

end VerifiableInference
