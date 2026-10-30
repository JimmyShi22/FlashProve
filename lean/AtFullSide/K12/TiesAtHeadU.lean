-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/TiesAtHeadU.lean

What it proves. The premise on the book of random values that our laws on a proximity test's pair of
parts take (hT: the test tiesB says yes at the job's place and number of members), from "the book is
the maker's": in the goals' scope, at any job at the folded row's test's place with two members or
at the request's own test's place with three (hT_of_made); and under the head at the very job of
onFreeT_head_U and sentence_and_condition_U (hT_head_U).

Names.
  hT_of_made   at any such job.
  hT_head_U    at jobHeadU's test.

By what. ties_at_laid (TiesAtLaid.lean in this folder). p12At_place, placeU, placeW, fourOf
(Johnson/Desc/ProofFile/Honest/K12/AtProof/Places.lean). The texts of jobHeadU
(Johnson/Desc/ProofFile/Honest/K12/OnFreeTAtHeadU.lean), jobLocU (JobsLocU.lean), jobAtU
(JobShared.lean), ManyJob.toRun (RunMany.lean), RunJob.toTest (RunJob.lean).

Limits.
- TiesAtLaid.lean's limits stand: the full size alone; the library's written sendings; the merges
  that the maker reads off the first chain; the side library.
- That a filling's book is the maker's at these letters is a premise (hB).
- Neither law that takes hT is applied here.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtLaid
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Block)
open Desc.K14 (St)
open ProofFile.Honest (ProverCoinCounts Common Weights TableRand Front bookWhole mergesByName)
open ProofFile.Honest.K12 (tiesB TestJob)
open ProofFile.Honest.K12.Light (jobHeadU)
open ProofFile.Honest.K12.AtProof (placeU placeW p12At_place)
open Johnson.G (proofSendsFull)
open P5J (TS)

/-- The premise hT of our laws on the pair, at any job at the folded row's test's place with two
members, or at the request's own test's place with three: from "Bk is the maker's book". -/
theorem hT_of_made {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {W X : Type} (J : TestJob W X)
    (hJ : (J.p.place = placeU ∧ J.members.length = 2) ∨
      (J.p.place = placeW ∧ J.members.length = 3)) :
    tiesB Bk J.p.place J.members.length = true := by
  obtain ⟨hU, hW⟩ := ties_at_laid scope L hB
  rcases hJ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact hU
  · rw [h1, h2]
    exact hW

/-- **The premise hT of onFreeT_head_U and of sentence_and_condition_U, at their own job, under the
head, from "Bk is the maker's book".** -/
theorem hT_head_U {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {W₀ Rc X₀ : Type} (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (u? : Option (Common W₀ Rc TableKey → Front X₀ → ℕ → OnBytes.E)) :
    tiesB Bk (jobHeadU Zp Np bs st weights rand u?).toRun.toTest.p.place
      (jobHeadU Zp Np bs st weights rand u?).toRun.toTest.members.length = true :=
  hT_of_made h.scope h.laid hB _ (Or.inl ⟨p12At_place _ _, rfl⟩)

end AtFullSide.K12

#print axioms AtFullSide.K12.hT_of_made
#print axioms AtFullSide.K12.hT_head_U
