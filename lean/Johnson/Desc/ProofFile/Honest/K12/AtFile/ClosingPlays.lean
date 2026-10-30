-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingPlays.lean: `Plays`, and so `PlaysS`, at the first
chain's closing proximity test, at its job `jobL`, with the run's three clauses paid from the thread
and the test on the book, and the test's new trees from the thread's tables.

  `s₀_of_stages`   the job's first stage
  `plays_jobL`     `Plays` at the test's number of the thread

By what. `plays_at_L` (ClosingAtL.lean); `agree_at_L` (ClosingRun.lean); `rowsOfHeard_jobL`
(ClosingJob.lean); `trees_of_thr` (K12/TreesOfThr.lean); `Thread.Made` for the count of trees.

Hypotheses. H, hb, hst, hk: `plays_at_L`'s. Pn: the plan: `planPlays_head_L` (ClosingLinesHead.lean).
hsent: the trees in front: `treesTo_354` (K12/OffAt354.lean). hT: the test on the book:
`hT_head_L` (AtFullSide/K12/TiesAtHeadL.lean). hold: each old opening is at hand at a stand with the
declared width. hks, hrs, hcount: public, on the plan. own₀: any value of the prover's own part. htable,
hfixed: the thread's tables of the test's own trees are the test's, fixed by the rounds in front of
the sending: letters' facts.

Limits.
- hold, htable and hfixed are asked: they read the thread's table, a letter. A thread whose table
  does not meet them is no instance.
- That a stand of the thread is reached is not said.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `plays_jobL` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the thread from `Thr` as a premise, `Plays` as its
end.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingAtL
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingRun
import Johnson.Desc.ProofFile.Honest.K12.TreesOfThr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts enterFinish)
open VerifiableInference.Desc.First (S)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (jobL rowsOfHeard_jobL)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

theorem s₀_of_stages {W Y : Type} {J : TestJob W Y} {s : Fmt.M1.Stage} {l : List Fmt.M1.Stage}
    (h : J.p.nums.stages = s :: l) : J.s₀ = s := by
  unfold TestJob.s₀
  rw [h]
  rfl

/-- **The closing test plays, at its job.** -/
theorem plays_jobL (L : ProofFile.Honest.FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : ℕ} (q : P12)
    (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
    {leave : S → T12 → Except String S} {start : Local W₀ Rc Xi Tr → S} {fall : T12}
    {blk : Block S Cl} {pre t : List (Block S Cl)}
    (H : LetterAtL L b (jobL q door D readers closing p) leave start fall blk pre t)
    (hb : L.thread.bs[b]? = some blk) (s u : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : (jobL q door D readers closing p).p.nums.stages = s :: u :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (sent : ℕ)
    (Pn : PlanPlays (jobL q door D readers closing p) s (u :: rest) sent)
    (hsent : treesTo L.thread.bs b = sent)
    (hT : tiesB Bk (jobL q door D readers closing p).p.place
      (jobL q door D readers closing p).members.length = true)
    (hold : ∀ k st m E, Thr L.thread b k st m E →
      ∀ d ∈ (proximityTestKind guardedProximityTestParts (jobL q door D readers closing p).p : Block T12 Unit).rounds,
        ∀ o ∈ d.opens, oldSrc E.sent o.2 = true → ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W)
    (hks : ∀ a ∈ (jobL q door D readers closing p).p.nums.stages, a.h ≤ a.k)
    (hrs : (blk.rounds.zip blk.oracles).length =
      firstLen (jobL q door D readers closing p).p.nums.stages +
        restLen (jobL q door D readers closing p).p.nums.stages)
    (hcount : (blk.oracles.flatMap id).length + 1 =
      (jobL q door D readers closing p).p.nums.stages.length)
    (hpl : blk.place = (jobL q door D readers closing p).p.place) (own₀ : X)
    (htable : ∀ τ, τ + 1 < (jobL q door D readers closing p).p.nums.stages.length →
      L.thread.table (.own (treesTo L.thread.bs b + τ)) =
        testTbl L.thread.chain (jobL q door D readers closing p) own₀
          (L.thread.front + roundsTo L.thread.bs b) (fun _ _ _ => true) τ)
    (hfixed : ∀ τ, τ + 1 < (jobL q door D readers closing p).p.nums.stages.length →
      L.thread.fixed (.own (treesTo L.thread.bs b + τ)) =
        L.thread.front + roundsTo L.thread.bs b +
          seedRound (jobL q door D readers closing p).p.nums.stages τ) :
    Plays L.thread b := by
  have hs₀ := s₀_of_stages hst
  have hk' : (jobL q door D readers closing p).s₀.k =
      (sgOf (jobL q door D readers closing p).s₀).h +
        (sgOf (jobL q door D readers closing p).s₀).g := by
    rw [hs₀]
    exact hk
  refine plays_at_L H hb sent s u rest hst hk Pn
    (fun k st m E _ c hA _ hc => ⟨?_, ?_, hold k st m E hA⟩) ?_
  · exact agree_at_L q D readers closing p _ rfl rfl rfl Bk _ _ c hc _ _ hT hk'
  · have hA' := hA
    unfold Thr Thread.Made at hA'
    obtain ⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩ := hA'
    rw [h3, hsent]
  · exact trees_of_thr L.thread hb _ rfl (rowsOfHeard_jobL q door D readers closing p) hks s u rest
      hst hpl (by rw [hpl]; exact H.half) hrs hcount own₀ htable hfixed

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.s₀_of_stages
#print axioms ProofFile.Honest.K12.plays_jobL
