-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/NotComplete.lean

When an argument system is not complete in the sense of `Complete`
(VerifiableInference/Statements.lean).

`Complete` asks that the honest committer and prover are rejected with probability at most α, for
all weights, every prompt and the model's output tokens on it. If the verifier rejects one such
instance whatever the hash function, the commitment and the proof are, the honest parties are
rejected there with probability 1: `not_complete_of_rejected`. The file is general: it holds for
every argument system. It does not bear on soundness.
-/
import VerifiableInference.Bridge

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

open RandomizedAlgorithm

/-- An event of probability 1 under every hash function has probability 1. -/
theorem Prob_eq_one {α : Type} (experiment : RandomizedAlgorithm α) (event : Set α)
    (h : ∀ hash, eventProbability (experiment.run hash) event = 1) : Prob experiment event = 1 := by
  unfold Prob
  simp only [h]
  rw [MeasureTheory.lintegral_one, uniformHash_eq]
  exact MeasureTheory.measure_univ

/-- If the verifier of an argument system rejects some instance whose output tokens are the
model's, under every hash function, every commitment and every proof, then the system is not
complete with any bound below 1. -/
theorem not_complete_of_rejected (system : ArgumentSystem) (weights : system.Weights)
    (prompt output : List Token) (isModelOutput : system.IsModelOutput weights prompt output)
    (rejected : ∀ hash commitment proof,
      system.accepts hash commitment prompt output proof = false)
    {α : ℝ≥0∞} (below : α < 1) : ¬ Complete system α := by
  intro complete
  refine absurd (lt_of_le_of_lt (complete weights prompt output isModelOutput) below)
    (not_lt.2 (le_of_eq (Eq.symm ?_)))
  refine Prob_eq_one _ _ fun hash => ?_
  show eventProbability ((system.sampleCommitmentRandomness.bind fun randomness =>
      ((system.commit weights randomness).toRandomized).bind fun commitment =>
        (system.prove weights randomness prompt output).bind fun proof =>
          (system.verify commitment prompt output proof).toRandomized).run hash)
    {accepted | accepted = false} = 1
  have last : ∀ commitment proof,
      ((system.verify commitment prompt output proof).toRandomized).run hash = PMF.pure false :=
    fun commitment proof => by
      rw [DeterministicAlgorithm.run_toRandomized]
      exact congrArg PMF.pure (rejected hash commitment proof)
  simp only [run_bind, last, PMF.bind_const]
  unfold eventProbability
  rw [PMF.toOuterMeasure_pure_apply]
  exact if_pos rfl

end VerifiableInference

#print axioms VerifiableInference.Prob_eq_one
#print axioms VerifiableInference.not_complete_of_rejected
