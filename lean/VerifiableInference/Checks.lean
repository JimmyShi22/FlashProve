-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Checks.lean

Proved facts about the statements of VerifiableInference/Statements.lean. None of them is about
this library's proof system:
  * the verifier step of an experiment returns the verifier's decision under the hash function
    (`ArgumentSystem.run_verify`);
  * `SoundAndBinding` gives `Sound`, and the form for an opened commitment (`SoundOpened`) with
    2 ε for ε (`sound_of_soundAndBinding`, `soundOpened_of_soundAndBinding`);
  * soundness alone, and completeness alone, are met by an argument system of no use
    (`rejectAll_sound`, `acceptAll_complete`).
The proofs use VerifiableInference/Bridge.lean, and through it ZKCP/Lemmas.lean of the
library for the calculus of probabilities.
-/
import VerifiableInference.Bridge

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

/-! ## 1. The verifier step of the experiments returns the verifier's decision -/

/-- The verifier step of the experiments returns the verifier's decision.
Under every hash function, the verifier step of an experiment returns `system.accepts hash
commitment prompt output proof` with probability 1. -/
theorem ArgumentSystem.run_verify (system : ArgumentSystem) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token)
    (proof : system.Proof) :
    ((system.verify commitment prompt output proof).toRandomized).run hash
      = PMF.pure (system.accepts hash commitment prompt output proof) :=
  DeterministicAlgorithm.run_toRandomized hash _

/-! ## 2. From `SoundAndBinding` to `Sound` and to the form for an opened commitment -/

/-- `SoundAndBinding` gives `Sound`, with the same extractor and the same ε. -/
theorem sound_of_soundAndBinding (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞)
    (h : SoundAndBinding system ε) : Sound system ε := by
  obtain ⟨extractor, h0⟩ := h
  exact ⟨extractor, fun committerQueries proverQueries State committer hC prover hP =>
    (h0 committerQueries proverQueries State committer hC).1 prover hP⟩

/-- `SoundAndBinding` gives the form for an opened commitment, with 2 ε for ε. -/
theorem soundOpened_of_soundAndBinding (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞)
    (h : SoundAndBinding system ε) :
    SoundOpened system (fun queries => 2 * ε queries) := by
  classical
  obtain ⟨extractor, h0⟩ := h
  intro queries adversary hq
  -- the committer runs the adversary and keeps its whole result as the state; the prover and the
  -- opener read their parts from it
  obtain ⟨h1, h2⟩ := h0 queries 0 _ (adversary.bind fun o => .done (o.1, o))
      (queryBound_map _ adversary queries hq)
  have b1 := h1 (fun state => .done state.2.2) (fun _ => trivial)
  have b2 := h2 (fun state => .done state.2.1) (fun _ => trivial)
  show Prob _ _ ≤ 2 * ε queries
  rw [two_mul]
  refine le_trans ?_ (add_le_add b1 b2)
  unfold Prob
  rw [← lintegral_add_right _ (measurable_eventProbability_run _ _)]
  refine lintegral_mono fun H => ?_
  -- the three experiments under one hash function H, as averages over the adversary's run with its
  -- query log
  have e0 : (adversary.bind fun o => (system.commit o.2.1.1 o.2.1.2).toRandomized.bind fun
      recomputed =>
        (system.verify o.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (o.1, recomputed, o.2.1.1, o.2.2.1, o.2.2.2.1, accepted)).run H
      = (adversary.withQueryLog.run H).bind fun ol => PMF.pure
          (ol.1.1, (system.commit ol.1.2.1.1 ol.1.2.1.2).evaluate H, ol.1.2.1.1,
          ol.1.2.2.1, ol.1.2.2.2.1, (system.verify ol.1.1 ol.1.2.2.1 ol.1.2.2.2.1
              ol.1.2.2.2.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done]
    conv_lhs => rw [← run_withQueryLog_fst H adversary]
    rw [PMF.bind_bind]
    simp only [PMF.pure_bind]
  have e1 : ((adversary.bind fun o => RandomizedAlgorithm.done (o.1, o)).withQueryLog.bind fun x =>
        (system.verify x.1.1 x.1.2.2.2.1 x.1.2.2.2.2.1 x.1.2.2.2.2.2).toRandomized.bind fun accepted
            =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, x.1.2.2.2.1, x.1.2.2.2.2.1, accepted)).run
              H
      = (adversary.withQueryLog.run H).bind fun ol => PMF.pure
          (extractor ol.1.1 ol.2, ol.1.2.2.1, ol.1.2.2.2.1,
          (system.verify ol.1.1 ol.1.2.2.1 ol.1.2.2.2.1 ol.1.2.2.2.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
        run_withQueryLog_map, PMF.bind_bind]
  have e2 : ((adversary.bind fun o => RandomizedAlgorithm.done (o.1, o)).withQueryLog.bind fun x =>
        (system.commit x.1.2.2.1.1 x.1.2.2.1.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, x.1.1, x.1.2.2.1.1, recomputed)).run H
      = (adversary.withQueryLog.run H).bind fun ol => PMF.pure
          (extractor ol.1.1 ol.2, ol.1.1, ol.1.2.1.1,
          (system.commit ol.1.2.1.1 ol.1.2.1.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
        run_withQueryLog_map, PMF.bind_bind]
  show ZKCP.prob ((adversary.bind fun o => (system.commit o.2.1.1 o.2.1.2).toRandomized.bind fun
      recomputed =>
        (system.verify o.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (o.1, recomputed, o.2.1.1, o.2.2.1, o.2.2.2.1, accepted)).run H)
              _
    ≤ ZKCP.prob (((adversary.bind fun o => RandomizedAlgorithm.done (o.1, o)).withQueryLog.bind fun
        x =>
        (system.verify x.1.1 x.1.2.2.2.1 x.1.2.2.2.2.1 x.1.2.2.2.2.2).toRandomized.bind fun accepted
            =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, x.1.2.2.2.1, x.1.2.2.2.2.1, accepted)).run
              H) _
      + ZKCP.prob (((adversary.bind fun o => RandomizedAlgorithm.done (o.1, o)).withQueryLog.bind
          fun x =>
        (system.commit x.1.2.2.1.1 x.1.2.2.1.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, x.1.1, x.1.2.2.1.1, recomputed)).run H) _
  rw [e0, e1, e2, ZKCP.prob_bind, ZKCP.prob_bind, ZKCP.prob_bind, ← ZKCP.expect_add]
  refine ZKCP.expect_mono _ fun ol => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure, ZKCP.prob_pure]
  -- for one run: if the commitment is opened to the weights, the verifier accepts and the output
  -- tokens are not the model's, then either
  -- the extractor gives these weights (first event) or it does not (second event)
  refine ind_le_add ?_
  rintro ⟨hCommitment, hAccepted, hNotOutput⟩
  by_cases hExtracted : extractor ol.1.1 ol.2 = some ol.1.2.1.1
  · left
    show (system.verify ol.1.1 ol.1.2.2.1 ol.1.2.2.2.1 ol.1.2.2.2.2).evaluate H = true
      ∧ ¬ ∃ weights, extractor ol.1.1 ol.2 = some weights ∧ system.IsModelOutput weights ol.1.2.2.1
          ol.1.2.2.2.1
    refine ⟨hAccepted, ?_⟩
    rintro ⟨weights', hWeights', hOutput'⟩
    rw [hExtracted] at hWeights'
    cases hWeights'
    exact hNotOutput hOutput'
  · right
    show (system.commit ol.1.2.1.1 ol.1.2.1.2).evaluate H = ol.1.1 ∧ extractor ol.1.1 ol.2 ≠ some
        ol.1.2.1.1
    exact ⟨hCommitment, hExtracted⟩

/-! ## 3. Soundness alone, and completeness alone, are met by an argument system of no use -/

/-- An argument system whose verifier rejects everything. -/
def rejectAll : ArgumentSystem where
  Weights := Unit
  PublicParameters := Unit
  publicParameters := id
  CommitmentRandomness := Unit
  Proof := Unit
  nextToken _ _ := none
  sampleCommitmentRandomness := .done ()
  commit _ _ := .done (fun _ => false)
  prove _ _ _ _ := .done ()
  verify _ _ _ _ := .done false

/-- Soundness alone is met by a verifier that rejects everything, with ε = 0, also in the form with
opening-form binding of the commitment (`rejectAll` has one value of weights, which the extractor
returns). -/
theorem rejectAll_soundAndBinding : SoundAndBinding rejectAll (fun _ => 0) := by
  refine ⟨fun _ _ => some (), fun committerQueries proverQueries State committer _ =>
      ⟨fun prover _ => ?_, fun opener _ => ?_⟩⟩
  · refine le_of_eq (Prob_eq_zero _ _ fun H => ?_)
    show ZKCP.prob ((committer.withQueryLog.bind fun x => (prover x.1.2).bind fun y =>
      RandomizedAlgorithm.done (some (), y.1, y.2.1, false)).run H) _ = 0
    rw [run_bind, ZKCP.prob_bind]
    refine (ZKCP.expect_congr _ fun c => ?_).trans (ZKCP.expect_const _ 0)
    rw [run_bind, ZKCP.prob_bind]
    refine (ZKCP.expect_congr _ fun p => ?_).trans (ZKCP.expect_const _ 0)
    show ZKCP.prob (PMF.pure _) _ = 0
    rw [ZKCP.prob_pure, if_neg]
    rintro ⟨h, -⟩
    exact Bool.false_ne_true h
  · refine le_of_eq (Prob_eq_zero _ _ fun H => ?_)
    show ZKCP.prob ((committer.withQueryLog.bind fun x => (opener x.1.2).bind fun y =>
      RandomizedAlgorithm.done (some (), x.1.1, y.1, (fun _ => false : Commitment))).run H) _ = 0
    rw [run_bind, ZKCP.prob_bind]
    refine (ZKCP.expect_congr _ fun c => ?_).trans (ZKCP.expect_const _ 0)
    rw [run_bind, ZKCP.prob_bind]
    refine (ZKCP.expect_congr _ fun p => ?_).trans (ZKCP.expect_const _ 0)
    show ZKCP.prob (PMF.pure _) _ = 0
    rw [ZKCP.prob_pure, if_neg]
    rintro ⟨-, h⟩
    exact h rfl

/-- The same for `Sound`. -/
theorem rejectAll_sound : Sound rejectAll (fun _ => 0) := sound_of_soundAndBinding rejectAll _
    rejectAll_soundAndBinding

/-- An argument system whose verifier accepts everything. -/
def acceptAll : ArgumentSystem where
  Weights := Unit
  PublicParameters := Unit
  publicParameters := id
  CommitmentRandomness := Unit
  Proof := Unit
  nextToken _ _ := none
  sampleCommitmentRandomness := .done ()
  commit _ _ := .done (fun _ => false)
  prove _ _ _ _ := .done ()
  verify _ _ _ _ := .done true

/-- Completeness alone is met by a verifier that accepts everything, with α = 0. -/
theorem acceptAll_complete : Complete acceptAll 0 := by
  intro weights prompt output _
  refine le_of_eq (Prob_eq_zero _ _ fun H => ?_)
  show ZKCP.prob (PMF.pure true) _ = 0
  rw [ZKCP.prob_pure, if_neg]
  intro h
  exact Bool.noConfusion h

end VerifiableInference
