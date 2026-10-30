-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Steps.lean

Completeness on a stated set of instances, `CompleteOn`: a weaker form of `Complete`. `Complete` is
`CompleteOn` with no side condition (`complete_iff_completeOn`).
-/
import VerifiableInference.Statements

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-- Completeness on a stated set of instances: as `Complete`, for the weights, prompts and output
tokens in `domain` only.
The definition has no other condition but "the output tokens are the model's"; a condition on the
weights may also be in the system's type `Weights`. -/
def CompleteOn (system : ArgumentSystem) (domain : system.Weights → List Token → List Token → Prop)
    (α : ℝ≥0∞) : Prop :=
  ∀ (weights : system.Weights) (prompt output : List Token),
    domain weights prompt output → system.IsModelOutput weights prompt output →
      Prob (do
          let randomness ← system.sampleCommitmentRandomness
          let commitment ← (system.commit weights randomness).toRandomized
          let proof ← system.prove weights randomness prompt output
          (system.verify commitment prompt output proof).toRandomized)
        {accepted | accepted = false}
        ≤ α

/-- `Complete` is `CompleteOn` with no side condition. -/
theorem complete_iff_completeOn (system : ArgumentSystem) (α : ℝ≥0∞) :
    Complete system α ↔ CompleteOn system (fun _ _ _ => True) α :=
  ⟨fun h weights prompt output _ hOutput => h weights prompt output hOutput,
   fun h weights prompt output hOutput => h weights prompt output trivial hOutput⟩

end VerifiableInference
