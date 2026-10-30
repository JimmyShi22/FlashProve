-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/LabelledCarry.lean: what the reply gives.

 1. The reply at a request is the word, beside something that the prover gives.
-/
import VerifiableInference.Labelled
import VerifiableInference.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference

variable {Label : Type} (system : ArgumentSystem)
  (label : system.Weights → List Token × List Token → Label)

/-- **What the reply gives**: the word, beside something that the prover gives. -/
theorem reply_gives (weights : system.Weights) (randomness : system.CommitmentRandomness)
    (prompt output : List Token) (hash : Hash) (answer : Label × system.Proof)
    (given : (reply system label weights randomness prompt output).run hash answer ≠ 0) :
    answer.1 = label weights (prompt, output) ∧
      (system.prove weights randomness prompt output).run hash answer.2 ≠ 0 := by
  have inSupport : answer ∈ (((system.prove weights randomness prompt output).bind fun proof =>
      RandomizedAlgorithm.done (label weights (prompt, output), proof)).run hash).support :=
    (PMF.mem_support_iff _ _).2 given
  rw [run_bind] at inSupport
  obtain ⟨proof, proofGiven, isPair⟩ := (PMF.mem_support_bind_iff _ _ _).1 inSupport
  simp only [run_done, PMF.support_pure, Set.mem_singleton_iff] at isPair
  subst isPair
  exact ⟨rfl, (PMF.mem_support_iff _ _).1 proofGiven⟩

end VerifiableInference

#print axioms VerifiableInference.reply_gives
