-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/SameSystem.lean: two argument systems that differ in their committer and prover alone, where
these have the same value and law at every hash function, have the same completeness and the same zero
knowledge, with the same simulator and error: the experiments read the honest side through its result
at each fixed hash function, and a view holds the verifier's own queries. Nothing here is a goal.
-/
import VerifiableInference.MoreStatements
import VerifiableInference.Steps
import VerifiableInference.Bridge

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference

/-- The system with another honest committer and prover. -/
abbrev withHonest (base : ArgumentSystem)
    (commit' : base.Weights → base.CommitmentRandomness → DeterministicAlgorithm Commitment)
    (prove' : base.Weights → base.CommitmentRandomness → List Token → List Token →
      RandomizedAlgorithm base.Proof) : ArgumentSystem :=
  { base with commit := commit', prove := prove' }

section
variable {base : ArgumentSystem}
  {commit' : base.Weights → base.CommitmentRandomness → DeterministicAlgorithm Commitment}
  {prove' : base.Weights → base.CommitmentRandomness → List Token → List Token →
    RandomizedAlgorithm base.Proof}

theorem realSteps_congr
    (hP : ∀ hash w r p o, (prove' w r p o).run hash = (base.prove w r p o).run hash)
    (hash : Hash) (chooser : View base.Proof → Option (List Token × List Token))
    (w : base.Weights) (r : base.CommitmentRandomness) :
    ∀ (verifier : MaliciousVerifier base.Proof) (remaining : ℕ) (view : View base.Proof),
      (realSteps (withHonest base commit' prove') chooser w r verifier remaining view).run hash =
        (realSteps base chooser w r verifier remaining view).run hash
  | .stop, _, _ => rfl
  | .query input next, remaining, view => by
    simp only [realSteps, RandomizedAlgorithm.run]
    exact realSteps_congr hP hash chooser w r (next _) remaining _
  | .sample bound next, remaining, view => by
    simp only [realSteps, RandomizedAlgorithm.run]
    exact congrArg _ (funext fun draw => realSteps_congr hP hash chooser w r (next draw) remaining _)
  | .requestProof _, 0, _ => rfl
  | .requestProof next, remaining + 1, view => by
    simp only [realSteps]
    cases chooser view with
    | none => rfl
    | some request =>
      simp only [run_bind]
      rw [hP hash w r request.1 request.2]
      exact congrArg _ (funext fun proof =>
        realSteps_congr hP hash chooser w r (next request proof) remaining _)

theorem realExperiment_congr
    (hC : ∀ hash w r, (commit' w r).evaluate hash = (base.commit w r).evaluate hash)
    (hP : ∀ hash w r p o, (prove' w r p o).run hash = (base.prove w r p o).run hash)
    (verifier : Commitment → MaliciousVerifier base.Proof)
    (chooser : View base.Proof → Option (List Token × List Token)) (w : base.Weights)
    (proofCount : ℕ) (hash : Hash) :
    (realExperiment (withHonest base commit' prove') verifier chooser w proofCount).run hash =
      (realExperiment base verifier chooser w proofCount).run hash := by
  show (base.sampleCommitmentRandomness.bind fun r => (commit' w r).toRandomized.bind fun c =>
      realSteps (withHonest base commit' prove') chooser w r (verifier c) proofCount
        ⟨c, [], [], []⟩).run hash =
    (base.sampleCommitmentRandomness.bind fun r => (base.commit w r).toRandomized.bind fun c =>
      realSteps base chooser w r (verifier c) proofCount ⟨c, [], [], []⟩).run hash
  rw [run_bind, run_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [run_bind, run_bind, DeterministicAlgorithm.run_toRandomized,
    DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, PMF.pure_bind, hC hash w r]
  exact realSteps_congr hP hash chooser w r _ proofCount _

/-- **Zero knowledge reads the honest side through its result at each hash function.** -/
theorem zeroKnowledgeOn_congr
    (hC : ∀ hash w r, (commit' w r).evaluate hash = (base.commit w r).evaluate hash)
    (hP : ∀ hash w r p o, (prove' w r p o).run hash = (base.prove w r p o).run hash)
    {domain : base.Weights → List Token → List Token → Prop} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : ZeroKnowledgeOn base domain ζ) :
    ZeroKnowledgeOn (withHonest base commit' prove') domain ζ := by
  obtain ⟨simulator, hs⟩ := h
  refine ⟨simulator, fun w chooser hc queries verifier proofCount hq => ?_⟩
  obtain ⟨h1, h2⟩ := hs w chooser hc queries verifier proofCount hq
  refine ⟨?_, h2⟩
  have e : Prob (realExperiment (withHonest base commit' prove') verifier chooser w proofCount) =
      Prob (realExperiment base verifier chooser w proofCount) :=
    funext fun E => Prob_congr_run (realExperiment_congr hC hP verifier chooser w proofCount) E
  rw [e]
  exact h1

/-- **Completeness reads the honest side through its result at each hash function.** -/
theorem completeOn_congr
    (hC : ∀ hash w r, (commit' w r).evaluate hash = (base.commit w r).evaluate hash)
    (hP : ∀ hash w r p o, (prove' w r p o).run hash = (base.prove w r p o).run hash)
    {domain : base.Weights → List Token → List Token → Prop} {α : ℝ≥0∞}
    (h : CompleteOn base domain α) :
    CompleteOn (withHonest base commit' prove') domain α := by
  intro w prompt output hd hm
  refine le_of_eq_of_le (Prob_congr_run (fun hash => ?_) _) (h w prompt output hd hm)
  show (base.sampleCommitmentRandomness.bind fun r => (commit' w r).toRandomized.bind fun c =>
      (prove' w r prompt output).bind fun π => (base.verify c prompt output π).toRandomized).run hash =
    (base.sampleCommitmentRandomness.bind fun r => (base.commit w r).toRandomized.bind fun c =>
      (base.prove w r prompt output).bind fun π =>
        (base.verify c prompt output π).toRandomized).run hash
  rw [run_bind, run_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [run_bind, run_bind, DeterministicAlgorithm.run_toRandomized,
    DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, PMF.pure_bind, hC hash w r, run_bind,
    run_bind, hP hash w r prompt output]

end

end VerifiableInference

#print axioms VerifiableInference.zeroKnowledgeOn_congr
#print axioms VerifiableInference.completeOn_congr
