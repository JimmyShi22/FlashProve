-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/SeveralCommitments.lean

From soundness for one commitment to soundness when one committer publishes several commitments
(VerifiableInference/MoreStatements.lean), and back, for every argument system.
`SoundForWith.severalCommitments`: the extractor stays the same, and the bound is multiplied by
`commitmentCount`: only the first `commitmentCount` places of the committer's list count.
`Sound.severalCommitments`: the same for `Sound`.
`SoundForSeveralCommitmentsWith.oneCommitment`, `SoundSeveralCommitments.sound`: back, at
`commitmentCount` = 1.
Limits. The factor comes from a union bound over the places of the list; nothing says how much of it
is needed. All commitments come from one run of the committer, whose whole query log the extractor
reads, and the prover starts after the last commitment is out. A commitment that is not among the
first `commitmentCount` of the list is not covered. A run has one proof.
The file is about no particular argument system.
-/
import VerifiableInference.MoreStatements
import VerifiableInference.Bridge
import ZKCP.Basic

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

/-- An element among the first `count` of a list is at a place below `count`. -/
theorem exists_getD_of_mem_take {α : Type} (fallback : α) :
    ∀ (count : ℕ) (list : List α) (element : α), element ∈ list.take count →
      ∃ index, index < count ∧ list.getD index fallback = element
  | 0, _, _, h => by simp at h
  | _ + 1, [], _, h => by simp at h
  | count + 1, head :: tail, element, h => by
      rw [List.take_succ_cons, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨0, Nat.succ_pos count, by simp [h]⟩
      · obtain ⟨index, hIndex, hElement⟩ := exists_getD_of_mem_take fallback count tail element h
        exact ⟨index + 1, Nat.succ_lt_succ hIndex, by simpa using hElement⟩

/-- From one commitment to several, for every argument system, every extractor and every claim: if
soundness for the claim holds with the bound ε (`SoundForWith`), then
`SoundForSeveralCommitmentsWith` holds with the same extractor and the bound
`commitmentCount * ε queries`. -/
theorem SoundForWith.severalCommitments (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
    (sound : SoundForWith system extractor claim ε) :
    SoundForSeveralCommitmentsWith system extractor claim fun queries commitmentCount =>
      commitmentCount * ε queries := by
  classical
  intro committerQueries proverQueries commitmentCount State committer committerBound prover
    proverBound
  show Prob _ _ ≤ (commitmentCount : ℝ≥0∞) * ε (committerQueries + proverQueries)
  -- for each place of the list: the committer that returns the commitment at that place (the same
  -- queries, the same query log), and the prover that drops the commitment from its result
  have one := fun index : ℕ => sound committerQueries proverQueries State
    (committer.bind fun o => .done (o.1.getD index (fun _ => false), o.2))
    (queryBound_map _ committer committerQueries committerBound)
    (fun state => (prover state).bind fun sent => .done sent.2)
    (fun state => queryBound_map _ (prover state) proverQueries (proverBound state))
  have total : ∑ _index ∈ Finset.range commitmentCount, ε (committerQueries + proverQueries)
      = commitmentCount * ε (committerQueries + proverQueries) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← total]
  refine le_trans ?_ (Finset.sum_le_sum fun index _ => one index)
  unfold Prob
  refine le_trans ?_ (le_of_eq (lintegral_finset_sum (Finset.range commitmentCount)
    fun index _ => measurable_eventProbability_run _ _))
  refine lintegral_mono fun H => ?_
  -- under one hash function H, all experiments are averages over the same two runs
  show ZKCP.prob ((committer.withQueryLog.bind fun x => (prover x.1.2).bind fun sent =>
        (system.verify sent.1 sent.2.1 sent.2.2.1 sent.2.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (x.1.1.take commitmentCount, sent.1, extractor sent.1 x.2,
            sent.2.1, sent.2.2.1, accepted)).run H) _
    ≤ ∑ index ∈ Finset.range commitmentCount,
      ZKCP.prob (((committer.bind fun o => RandomizedAlgorithm.done
          (o.1.getD index (fun _ => false), o.2)).withQueryLog.bind fun x =>
        ((prover x.1.2).bind fun sent => RandomizedAlgorithm.done sent.2).bind fun y =>
        (system.verify x.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, y.1, y.2.1, accepted)).run H) _
  simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
    run_withQueryLog_map, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_pure]
  rw [← ZKCP.expect_finset_sum]
  refine ZKCP.expect_mono _ fun x => ?_
  rw [← ZKCP.expect_finset_sum]
  refine ZKCP.expect_mono _ fun sent => ?_
  split_ifs with bad
  · obtain ⟨hAccepted, hMember, hNot⟩ := bad
    obtain ⟨index, hIndex, hAt⟩ :=
      exists_getD_of_mem_take (fun _ => false) commitmentCount x.1.1 sent.1 hMember
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_range.2 hIndex))
    refine le_of_eq (if_pos ?_).symm
    rw [hAt]
    exact And.intro hAccepted hNot
  · exact zero_le _

/-- Back: the statement for several commitments gives the statement for one, with the same extractor
and the bound at `commitmentCount` = 1. -/
theorem SoundForSeveralCommitmentsWith.oneCommitment (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℕ → ℝ≥0∞)
    (sound : SoundForSeveralCommitmentsWith system extractor claim ε) :
    SoundForWith system extractor claim fun queries => ε queries 1 := by
  classical
  intro committerQueries proverQueries State committer committerBound prover proverBound
  -- the committer returns its one commitment as a list; the prover returns that commitment
  have several := sound committerQueries proverQueries 1 (Commitment × State)
    (committer.bind fun o => .done ([o.1], o))
    (queryBound_map _ committer committerQueries committerBound)
    (fun state => (prover state.2).bind fun sent => .done (state.1, sent))
    (fun state => queryBound_map _ (prover state.2) proverQueries (proverBound state.2))
  refine le_trans ?_ several
  unfold Prob
  refine lintegral_mono fun H => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun x => (prover x.1.2).bind fun sent =>
        (system.verify x.1.1 sent.1 sent.2.1 sent.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, sent.1, sent.2.1, accepted)).run H) _
    ≤ ZKCP.prob (((committer.bind fun o => RandomizedAlgorithm.done ([o.1], o)).withQueryLog.bind
        fun x =>
        ((prover x.1.2.2).bind fun sent => RandomizedAlgorithm.done (x.1.2.1, sent)).bind fun y =>
        (system.verify y.1 y.2.1 y.2.2.1 y.2.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (x.1.1.take 1, y.1, extractor y.1 x.2, y.2.1, y.2.2.1,
            accepted)).run H) _
  simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
    run_withQueryLog_map, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_pure]
  refine ZKCP.expect_mono _ fun x => ZKCP.expect_mono _ fun sent => ind_le ?_
  rintro ⟨hAccepted, hNot⟩
  exact And.intro hAccepted (And.intro (by simp) hNot)

/-- `Sound` gives `SoundSeveralCommitments`, with the bound multiplied by `commitmentCount`. -/
theorem Sound.severalCommitments (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) (sound : Sound system ε) :
    SoundSeveralCommitments system fun queries commitmentCount => commitmentCount * ε queries := by
  obtain ⟨extractor, soundWith⟩ := sound
  exact ⟨extractor, SoundForWith.severalCommitments system extractor system.IsModelOutput ε
    soundWith⟩

/-- `SoundSeveralCommitments` gives `Sound`, with the bound at `commitmentCount` = 1. -/
theorem SoundSeveralCommitments.sound (system : ArgumentSystem) (ε : ℕ → ℕ → ℝ≥0∞)
    (sound : SoundSeveralCommitments system ε) : Sound system fun queries => ε queries 1 := by
  obtain ⟨extractor, soundWith⟩ := sound
  exact ⟨extractor, SoundForSeveralCommitmentsWith.oneCommitment system extractor
    system.IsModelOutput ε soundWith⟩

end VerifiableInference

#print axioms VerifiableInference.SoundForWith.severalCommitments
#print axioms VerifiableInference.SoundForSeveralCommitmentsWith.oneCommitment
#print axioms VerifiableInference.Sound.severalCommitments
#print axioms VerifiableInference.SoundSeveralCommitments.sound
#print axioms VerifiableInference.exists_getD_of_mem_take
