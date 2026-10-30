-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ExtractsDrawn.lean: FROM THE OPENING FORM OF BINDING TO CORRECTNESS OF EXTRACTION,
general in the argument system. One theorem, with four equations by definition beneath it.
"Binding" in this file is the opening form, BindsWith (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give; at fixed randomness it yields that the extractor gives the
committed weights back (BindsWith.atRandomness). It is not the index binding of ZKCP/Defs.lean's
HasIndexBinding: soundness under the files' policy (G8bits, Ladder/Bits.lean) has that form, for the
claim "meets the policy" (the tie is typed at exact match: sound_iff,
VerifiableInference/Agreement.lean), and speaks of every commitment, whoever made it.

  **BindsWith.extractsDrawn** (namespace VerifiableInference): where the commitment binds to the
    extractor's weights with the bound ε, the sampler draws one number and maps it, and the
    committer asks at most q queries: ExtractsCommittedWeights
    (VerifiableInference/MoreStatements.lean) holds with the error ε q: from an honest commitment,
    at randomness that the system's own sampler draws, and that run's queries the extractor gives
    the honest committer's weights. Why: the honest committer, with the opener that hands back the
    weights and the drawn randomness, is one of the adversaries of BindsWith, and its opening always
    fits. The kin at given randomness: BindsWith.atRandomness
    (VerifiableInference/BindsAtRandomness.lean), whose text this follows.
Limits. A sampler that asks the hash function, or draws more than once, is not covered. Nothing on
any named system.
Terms: lean/GLOSSARY.md.

-/
import VerifiableInference.BindsAtRandomness
import VerifiableInference.MoreStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference
open RandomizedAlgorithm

private theorem bind_sample' {α β : Type} (N : ℕ) (next : Fin (N + 1) → RandomizedAlgorithm α)
    (rest : α → RandomizedAlgorithm β) :
    (RandomizedAlgorithm.sample N next).bind rest = .sample N fun d => (next d).bind rest := rfl

private theorem bind_done' {α β : Type} (a : α) (rest : α → RandomizedAlgorithm β) :
    (RandomizedAlgorithm.done a).bind rest = rest a := rfl

private theorem withQueryLog_sample' {α : Type} (N : ℕ)
    (next : Fin (N + 1) → RandomizedAlgorithm α) :
    (RandomizedAlgorithm.sample N next).withQueryLog = .sample N fun d => (next d).withQueryLog :=
  rfl

private theorem run_sample' {α : Type} (hash : Hash) (N : ℕ)
    (next : Fin (N + 1) → RandomizedAlgorithm α) :
    (RandomizedAlgorithm.sample N next).run hash =
      (PMF.uniformOfFintype (Fin (N + 1))).bind fun d => (next d).run hash := rfl

/-- **From binding to correctness of extraction**, where the sampler draws one number and maps it.
-/
theorem BindsWith.extractsDrawn {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {ε : ℕ → ℝ≥0∞}
    (binds : BindsWith system extractor ε) (N : ℕ) (f : Fin (N + 1) → system.CommitmentRandomness)
    (hs : system.sampleCommitmentRandomness = .sample N fun t => .done (f t)) (queries : ℕ)
    (bound : ∀ w r, (system.commit w r).toRandomized.QueryBound queries) :
    ExtractsCommittedWeights system extractor (ε queries) := by
  classical
  intro weights
  have key := binds queries 0 (Fin (N + 1))
    (.sample N fun t => (system.commit weights (f t)).toRandomized.bind fun c => .done (c, t))
    (fun t => queryBound_map _ _ _ (bound weights (f t)))
    (fun t => .done (weights, f t)) (fun _ => trivial)
  refine le_trans ?_ key
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob (((system.sampleCommitmentRandomness.bind fun randomness =>
        (system.commit weights randomness).toRandomized).withQueryLog.bind fun c =>
          RandomizedAlgorithm.done (extractor c.1 c.2)).run hash) _
    ≤ ZKCP.prob (((RandomizedAlgorithm.sample N fun t =>
        (system.commit weights (f t)).toRandomized.bind fun c =>
          RandomizedAlgorithm.done (c, t)).withQueryLog.bind fun c =>
        (RandomizedAlgorithm.done (weights, f c.1.2)).bind fun y =>
          (system.commit y.1 y.2).toRandomized.bind fun recomputed =>
            RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, y.1, recomputed)).run hash) _
  rw [hs]
  simp only [bind_sample', bind_done', withQueryLog_sample', run_sample']
  rw [ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun t => ?_
  rw [run_bind, run_bind, run_withQueryLog_map, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_le_on_support _ fun o ho => ?_
  have h1 : o.1 = (system.commit weights (f t)).evaluate hash := by
    have hm : o.1 ∈ (((system.commit weights (f t)).toRandomized.withQueryLog.run hash).bind
        fun out => PMF.pure out.1).support :=
      (PMF.mem_support_bind_iff _ _ _).2 ⟨o, ho, (PMF.mem_support_pure_iff _ _).2 rfl⟩
    rw [run_withQueryLog_fst, DeterministicAlgorithm.run_toRandomized] at hm
    exact (PMF.mem_support_pure_iff _ _).1 hm
  rw [PMF.pure_bind, run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
    run_done, ZKCP.prob_pure, ZKCP.prob_pure]
  exact ind_le fun hb => ⟨h1.symm, hb⟩

end VerifiableInference

#print axioms VerifiableInference.BindsWith.extractsDrawn
