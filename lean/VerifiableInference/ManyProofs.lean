-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/ManyProofs.lean

From soundness for one proof to soundness for several proofs under one commitment
(VerifiableInference/MoreStatements.lean), and back, for every argument system.
`SoundForWith.manyProofs`: if the verifier makes at most `verifierQueries` queries on every input,
soundness for a claim with the bound ε gives soundness for a list of proofs with the same extractor
and the bound ε (queries + proofCount · verifierQueries). `Sound.manyProofs`: the same for `Sound`.
`SoundForManyProofsWith.oneProof`, `SoundManyProofs.sound`: back, at `proofCount` = 1.
Limits. The list is sent at once: the prover sees no decision of the verifier before it sends the
list. Entries after the first `proofCount` are not checked. One commitment in each run. `proofCount`
times the verifier's bound is added to the adversary's queries, so for one proof the bound is ε at
`verifierQueries` more queries.
The file is about no particular argument system.
-/
import VerifiableInference.MoreStatements
import VerifiableInference.Bridge
import ZKCP.ManyOfOneLists

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

/-- Under a hash function, `verifyEach` returns with probability 1 the entries' prompts and output
tokens, each with the verifier's decision (`accepts`) under that hash function. -/
theorem run_verifyEach (system : ArgumentSystem) (hash : Hash) (commitment : Commitment) :
    ∀ sent : List (List Token × List Token × system.Proof),
      (system.verifyEach commitment sent).run hash = PMF.pure (sent.map fun entry =>
        (entry.1, entry.2.1, system.accepts hash commitment entry.1 entry.2.1 entry.2.2))
  | [] => rfl
  | (prompt, output, proof) :: rest => by
      show ((system.verify commitment prompt output proof).toRandomized.bind fun accepted =>
        (system.verifyEach commitment rest).bind fun others =>
          RandomizedAlgorithm.done ((prompt, output, accepted) :: others)).run hash = _
      rw [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_bind,
        run_verifyEach system hash commitment rest, PMF.pure_bind, run_done]
      rfl

/-- `SoundForWith` gives the same bound, under the same bounds on the queries, for a committer and a
prover of the type `ZKCP.OComp 256` (ZKCP/Defs.lean; the translation: Bridge.lean), with the
verifier's decision in the event. A lemma for `SoundForWith.manyProofs`: this is the form that
`ZKCP.ManyOfOneLists.many_of_one` takes. -/
theorem soundForWith_upload (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
    (sound : SoundForWith system extractor claim ε) (committerQueries proverQueries : ℕ)
    (State : Type) (committer : ZKCP.OComp 256 (Commitment × State))
    (prover : State → ZKCP.OComp 256 (List Token × List Token × system.Proof))
    (committerBound : committer.QueryBound committerQueries)
    (proverBound : ∀ state, (prover state).QueryBound proverQueries) :
    ZKCP.Pr (committer.withTrace.bind fun c => (prover c.1.2).bind fun entry =>
        ZKCP.OComp.pure (c.1.1, extractor c.1.1 c.2, entry))
      (fun hash => {o | (system.verify o.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).evaluate hash = true ∧
        ¬ ∃ weights, o.2.1 = some weights ∧ claim weights o.2.2.1 o.2.2.2.1})
      ≤ ε (committerQueries + proverQueries) := by
  refine le_trans ?_ (sound committerQueries proverQueries State (ofUpload committer)
    ((queryBound_ofUpload committer committerQueries).2 committerBound)
    (fun state => ofUpload (prover state))
    fun state => (queryBound_ofUpload (prover state) proverQueries).2 (proverBound state))
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((committer.withTrace.bind fun c => (prover c.1.2).bind fun entry =>
        ZKCP.OComp.pure (c.1.1, extractor c.1.1 c.2, entry)).run hash) _
    ≤ ZKCP.prob (((ofUpload committer).withQueryLog.bind fun c =>
        (ofUpload (prover c.1.2)).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run hash) _
  rw [ZKCP.run_bind, run_bind, run_ofUpload_withQueryLog, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [ZKCP.run_bind, run_bind, run_ofUpload, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun y => ?_
  rw [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done]
  show ZKCP.prob (PMF.pure _) _ ≤ ZKCP.prob (PMF.pure _) _
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le fun hb => ?_
  obtain ⟨h1, h2⟩ := hb
  exact ⟨h1, h2⟩

/-- From one proof to many, for every argument system, extractor and claim. If soundness for the
claim holds with the bound ε, and the verifier makes at most `verifierQueries` queries to the hash
function on every input, then soundness for a list of proofs holds with the same extractor and the
bound ε (queries + proofCount · verifierQueries); ε has no factor in front.
The proof (`ZKCP.ManyOfOneLists.many_of_one`, ZKCP/ManyOfOneLists.lean): a prover for one proof runs
the prover for many, runs the verifier on the first `proofCount` entries, and returns the first
accepted entry for which the claim fails at the extractor's result. -/
theorem SoundForWith.manyProofs (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
    (sound : SoundForWith system extractor claim ε) (verifierQueries : ℕ)
    (verifierBound : ∀ commitment prompt output proof,
      (system.verify commitment prompt output proof).toRandomized.QueryBound verifierQueries) :
    SoundForManyProofsWith system extractor claim fun queries proofCount =>
      ε (queries + proofCount * verifierQueries) := by
  intro committerQueries proverQueries proofCount State committer committerBound prover proverBound
  show Prob _ _ ≤ ε (committerQueries + proverQueries + proofCount * verifierQueries)
  by_cases hProof : Nonempty system.Proof
  · obtain ⟨proof₀⟩ := hProof
    have many := ZKCP.ManyOfOneLists.many_of_one
      (fun (commitment : Commitment) (entry : List Token × List Token × system.Proof) =>
        (system.verify commitment entry.1 entry.2.1 entry.2.2).toRandomized.toUpload)
      (fun hash commitment entry =>
        (system.verify commitment entry.1 entry.2.1 entry.2.2).evaluate hash)
      (fun hash commitment entry => (run_toUpload hash _).trans
        (DeterministicAlgorithm.run_toRandomized hash
          (system.verify commitment entry.1 entry.2.1 entry.2.2)))
      (fun commitment entry => (queryBound_toUpload _ verifierQueries).2
        (verifierBound commitment entry.1 entry.2.1 entry.2.2))
      extractor
      (fun _ extracted entry =>
        ∃ weights, extracted = some weights ∧ claim weights entry.1 entry.2.1)
      ([], [], proof₀) (fun tC tP => ε (tC + tP))
      (fun tC tP St Ct Pv hC hP =>
        soundForWith_upload system extractor claim ε sound tC tP St Ct Pv hC hP)
      committerQueries proverQueries proofCount State committer.toUpload
      (fun state => ((prover state).bind fun sent =>
        RandomizedAlgorithm.done (sent.take proofCount)).toUpload)
      ((queryBound_toUpload committer committerQueries).2 committerBound)
      (fun state => (queryBound_toUpload _ proverQueries).2
        (queryBound_map _ (prover state) proverQueries (proverBound state)))
    refine le_trans ?_ (many.trans_eq (congrArg ε
      (Nat.add_assoc committerQueries proverQueries (proofCount * verifierQueries)).symm))
    unfold Prob ZKCP.Pr ZKCP.PrCoins
    refine lintegral_mono fun hash => ?_
    show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun sent =>
          (system.verifyEach c.1.1 (sent.take proofCount)).bind fun checked =>
            RandomizedAlgorithm.done (extractor c.1.1 c.2, checked)).run hash) _
      ≤ ZKCP.prob ((committer.toUpload.withTrace.bind fun c =>
          (((prover c.1.2).bind fun sent =>
            RandomizedAlgorithm.done (sent.take proofCount)).toUpload).bind fun sent =>
            ZKCP.OComp.pure (c.1.1, extractor c.1.1 c.2, sent)).run hash) _
    rw [run_bind, ZKCP.run_bind, run_toUpload_withTrace, ZKCP.prob_bind, ZKCP.prob_bind]
    refine ZKCP.expect_mono _ fun c => ?_
    rw [run_bind, ZKCP.run_bind, run_toUpload, run_bind, PMF.bind_bind, ZKCP.prob_bind,
      ZKCP.prob_bind]
    refine ZKCP.expect_mono _ fun sent => ?_
    rw [run_bind, run_verifyEach, PMF.pure_bind, run_done, run_done, PMF.pure_bind]
    show ZKCP.prob (PMF.pure _) _ ≤ ZKCP.prob (PMF.pure _) _
    rw [ZKCP.prob_pure, ZKCP.prob_pure]
    refine ind_le fun hb => ?_
    obtain ⟨prompt, output, hMem, hBad⟩ := hb
    obtain ⟨entry, hEntry, hEq⟩ := List.mem_map.1 hMem
    obtain ⟨rfl, hEq'⟩ := Prod.mk.inj hEq
    obtain ⟨rfl, hAccepted⟩ := Prod.mk.inj hEq'
    show (sent.take proofCount).length ≤ proofCount ∧ ∃ a ∈ sent.take proofCount,
      (system.verify c.1.1 a.1 a.2.1 a.2.2).evaluate hash = true ∧
        ¬ ∃ weights, extractor c.1.1 c.2 = some weights ∧ claim weights a.1 a.2.1
    exact ⟨List.length_take_le _ _, entry, hEntry, hAccepted, hBad⟩
  · -- No proof exists: every list is empty, and the event has probability 0.
    refine le_trans (le_of_eq (Prob_eq_zero _ _ fun hash => ?_)) (zero_le _)
    show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun sent =>
          (system.verifyEach c.1.1 (sent.take proofCount)).bind fun checked =>
            RandomizedAlgorithm.done (extractor c.1.1 c.2, checked)).run hash) _ = 0
    refine le_antisymm ?_ (zero_le _)
    rw [run_bind, ZKCP.prob_bind]
    refine le_trans (ZKCP.expect_mono _ fun c => ?_) (le_of_eq (ZKCP.expect_const _ 0))
    rw [run_bind, ZKCP.prob_bind]
    refine le_trans (ZKCP.expect_mono _ fun sent => ?_) (le_of_eq (ZKCP.expect_const _ 0))
    rw [run_bind, run_verifyEach, PMF.pure_bind, run_done, ZKCP.prob_pure]
    refine le_of_eq (if_neg ?_)
    rintro ⟨prompt, output, hMem, -⟩
    obtain ⟨entry, -, -⟩ := List.mem_map.1 hMem
    exact hProof ⟨entry.2.2⟩

/-- Soundness for a list of proofs gives soundness for one proof, with the same extractor and the
bound at `proofCount` = 1: a prover for one proof is a prover that sends a list of one entry. So
`SoundForManyProofsWith` asks at least as much as `SoundForWith`. -/
theorem SoundForManyProofsWith.oneProof (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℕ → ℝ≥0∞)
    (sound : SoundForManyProofsWith system extractor claim ε) :
    SoundForWith system extractor claim fun queries => ε queries 1 := by
  intro committerQueries proverQueries State committer committerBound prover proverBound
  refine le_trans ?_ (sound committerQueries proverQueries 1 State committer committerBound
    (fun state => (prover state).bind fun entry => RandomizedAlgorithm.done [entry])
    fun state => queryBound_map _ (prover state) proverQueries (proverBound state))
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run hash) _
    ≤ ZKCP.prob ((committer.withQueryLog.bind fun c =>
        ((prover c.1.2).bind fun entry => RandomizedAlgorithm.done [entry]).bind fun sent =>
        (system.verifyEach c.1.1 (sent.take 1)).bind fun checked =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, checked)).run hash) _
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [run_bind, run_bind, run_bind, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun y => ?_
  rw [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done, run_done,
    PMF.pure_bind, run_bind, run_verifyEach, PMF.pure_bind, run_done, ZKCP.prob_pure,
    ZKCP.prob_pure]
  refine ind_le fun hb => ?_
  obtain ⟨h1, h2⟩ := hb
  have hAccepted : system.accepts hash c.1.1 y.1 y.2.1 y.2.2 = true := h1
  refine ⟨y.1, y.2.1, ?_, h2⟩
  show (y.1, y.2.1, true) ∈ [(y.1, y.2.1, system.accepts hash c.1.1 y.1 y.2.1 y.2.2)]
  rw [hAccepted]
  exact List.mem_singleton.2 rfl

/-- `Sound`, and a bound `verifierQueries` on the verifier's queries, give `SoundManyProofs` with
the bound ε (queries + proofCount · verifierQueries). -/
theorem Sound.manyProofs (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) (sound : Sound system ε)
    (verifierQueries : ℕ)
    (verifierBound : ∀ commitment prompt output proof,
      (system.verify commitment prompt output proof).toRandomized.QueryBound verifierQueries) :
    SoundManyProofs system fun queries proofCount =>
      ε (queries + proofCount * verifierQueries) := by
  obtain ⟨extractor, soundWith⟩ := sound
  exact ⟨extractor, SoundForWith.manyProofs system extractor system.IsModelOutput ε soundWith
    verifierQueries verifierBound⟩

/-- `SoundManyProofs` gives `Sound`, with the bound at `proofCount` = 1. -/
theorem SoundManyProofs.sound (system : ArgumentSystem) (ε : ℕ → ℕ → ℝ≥0∞)
    (sound : SoundManyProofs system ε) : Sound system fun queries => ε queries 1 := by
  obtain ⟨extractor, soundWith⟩ := sound
  exact ⟨extractor, SoundForManyProofsWith.oneProof system extractor system.IsModelOutput ε
    soundWith⟩

end VerifiableInference

#print axioms VerifiableInference.SoundForWith.manyProofs
#print axioms VerifiableInference.SoundForManyProofsWith.oneProof
#print axioms VerifiableInference.Sound.manyProofs
#print axioms VerifiableInference.SoundManyProofs.sound
#print axioms VerifiableInference.run_verifyEach
#print axioms VerifiableInference.soundForWith_upload
