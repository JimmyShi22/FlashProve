-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/TiesAtHeadW.lean

What it proves. The premise on the book of random values that five_at_second takes (hT: the test
tiesB says yes at the job's place and number of members), under the head, at the bare job at the
request's own proximity test (bareW, Johnson/Desc/ProofFile/Honest/K12/AtProof/MembersW.lean), from
"the book is the maker's".

Names.
  membersW_three   under the head the test's group as membersW lays it has three members.
  hT_head_W        the law.

By what. hT_of_made (TiesAtHeadU.lean in this folder). The library's AtMg.w_msgs
(Johnson/P5J/NumAtHead.lean): under the head W's sending holds two oracle messages. p12At_place,
fourOf, four (Johnson/Desc/ProofFile/Honest/K12/AtProof/Places.lean). The texts of membersW, parWAt,
bareW, of bareJob (AtProof/Doors.lean). Of the authors of the honest side of the shared sending
(K1): parW_sent (Johnson/Desc/ProofFile/Honest/K1/PlaceW.lean): W's sending holds just the message
handed in.

Limits.
- TiesAtLaid.lean's limits stand: the full size alone; the library's written sendings; the merges
  that the maker reads off the first chain; the side library.
- bareW is the bare job: its rows and trees are idle: a stand-in of public numbers for a test of the
  laying, no honest prover's side, not to be laid into a filling that is played or counted (the
  heads of AtProof/MembersW.lean and Bare.lean). hT reads the job's place and its number of members
  alone: a later job with these two is served by hT_of_made.
- That bareW returns a job is a premise (hJ); that a filling's book is the maker's at these letters
  is a premise (hB). five_at_second is not applied here.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtHeadU
import Johnson.Desc.ProofFile.Honest.K12.AtProof.MembersW
import Johnson.Desc.ProofFile.Honest.K1.PlaceW
import Johnson.P5J.NumAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (ProverCoinCounts Addr Due bookWhole mergesByName)
open ProofFile.Honest.K12 (tiesB TestJob)
open ProofFile.Honest.K12.AtProof (placeW p12At_place membersW parWAt bareW four fourOf bareJob)
open Johnson.G (proofSendsFull)
open P5J (TS)

/-- Under the head the group of the request's own test, as membersW lays it, has three members. -/
theorem membersW_three {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) (G : ProofFile.Ground) {ms : List (Addr × ℕ × Due)}
    (hm : membersW Zp G = some ms) : ms.length = 3 := by
  unfold membersW at hm
  obtain ⟨P, hP, hm⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hm
  unfold parWAt at hP
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hP
  have h2 : msg.size = 2 := by
    have e := h.w_msgs
    rw [hmsg] at e
    exact e
  have hs : (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg).sent.size = 2 := by
    rw [ProofFile.Honest.K1.parW_sent]
    exact h2
  simp [hs]

/-- **The premise hT of five_at_second, at the bare job at the request's own test (bareW), under the
head, from "Bk is the maker's book".** -/
theorem hT_head_W {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {W X : Type} (G : ProofFile.Ground) {J : TestJob W X} (hJ : bareW Zp G = some J) :
    tiesB Bk J.p.place J.members.length = true := by
  unfold bareW at hJ
  obtain ⟨F, hF, hJ⟩ := Option.bind_eq_some_iff.1 hJ
  obtain ⟨ms, hms, rfl⟩ := Option.map_eq_some_iff.1 hJ
  have hp : F.W.place = placeW := by
    unfold four at hF
    split at hF
    · obtain rfl := Option.some.inj hF
      exact p12At_place _ _
    · cases hF
  exact hT_of_made h.scope h.laid hB _ (Or.inr ⟨hp, membersW_three h G hms⟩)

end AtFullSide.K12

#print axioms AtFullSide.K12.membersW_three
#print axioms AtFullSide.K12.hT_head_W
