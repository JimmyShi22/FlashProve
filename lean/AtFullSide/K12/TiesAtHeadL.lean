-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/TiesAtHeadL.lean

What it proves. The premise on the book of random values that five_at_first takes (hT: the test
tiesB says yes at the job's place and number of members), under the head, at the lot's own job at
the first chain's proximity test (jobL, Johnson/Desc/ProofFile/Honest/K12/AtProof/JobL.lean), from
"the book is the maker's". Two hands meet in one number: the code switch's own reckoning of what its
finish carries (184 stretches, and the carrying message's own), and the maker's reading of the
library's sendings (tiesB says yes at 185).

Names.
  membersL_185   under the head, at the blank ground, the job has 185 members.
  hT_head_L      the law.

By what. ties_at_laid_L (TiesAtLaidL.lean in this folder). One evaluation in Lean's kernel, of a
length, at the library's written values. The library's prep_pinned (Johnson/IMR/SendsPinned.lean)
with pins_at_head (Johnson/Desc/First/Att/Door/Law/K5CondOfHead.lean); spots_at_head
(Johnson/AtFull/Shape/LinkNumbersAtHead.lean): under the head the places that have rounds are the
written list. numbersL_at_head (Johnson/Desc/ProofFile/Honest/K12/AtProof/LotAtDoor.lean);
p12At_place, fourOf (AtProof/Places.lean). The texts of finishAt, membersL, jobL (AtProof/JobL.lean)
and of K2.switchPlaces (Johnson/Desc/ProofFile/Honest/K2/Half.lean).

Limits.
- TiesAtLaidL.lean's limits stand: the full size alone; the library's written sendings; the merges
  that the maker reads off the first chain; the side library.
- At the blank ground (hG): prep_pinned's own premise. It is the ground at which the frame's onlineProverFromPublicFiles
  makes its filling.
- That finishAt returns a place is a premise (hf); that a filling's book is the maker's at these
  letters is a premise (hB). The job's door, rows' data, readers and closing are letters: hT reads
  none of them.
- tiesB compares owners and starts: the spent entry's count and the carried one's are not compared.
- five_at_first is not applied here.
- One limit is raised at one theorem (membersL_185): maxRecDepth to 1000000.
- What it costs: on our machine this file took 14 s to build; TiesAtLaidL.lean beneath it 734 s (at
  26.5 GiB resident) and, in a second build, 784 s (its room not measured).
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtLaidL
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotAtDoor
import Johnson.AtFull.Shape.LinkNumbersAtHead
import Johnson.Desc.First.Att.Door.Law.K5CondOfHead
import Johnson.IMR.SendsPinned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest (ProverCoinCounts Local Front RowDataOf Readers bookWhole mergesByName)
open ProofFile.Honest.K12 (tiesB)
open ProofFile.Honest.K12.AtProof (placeL p12At_place finishAt membersL jobL numbersL_at_head)
open ProofFile.Honest (K2.SwitchPlace K2.Closing)
open Johnson.G (proofSendsFull)
open P5J (TS)

set_option maxRecDepth 1000000 in
/-- **Under the head, at the blank ground, the job at the first chain's proximity test has 185
members**: the 184 stretches that the code switch's finish carries, by that kind's own reckoning
(K2.switchPlaces' field front), and the carrying message's own. -/
theorem membersL_185 {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) : (membersL pl).length = 185 := by
  have hp : P1K2.prepOf Zp G = IM.prepW :=
    IM.prep_pinned h.laid.pub (H2K5.Door.pins_at_head h).1 hG
  have hs : ProofFile.spotsOf Zp.cuts = some Johnson.AtFull.Desc.spotsWritten :=
    Johnson.AtFull.Shape.spots_at_head h
  have key : ((ProofFile.Honest.K2.switchPlaces Zp G).find? fun p => p.place.link.isNone).map
      (·.front.length) = some 184 := by
    unfold ProofFile.Honest.K2.switchPlaces
    rw [hp, hs]
    decide +kernel
  unfold finishAt at hf
  rw [hf] at key
  have h184 : pl.front.length = 184 := Option.some.inj key
  unfold membersL
  rw [List.length_append, h184]
  rfl

/-- **The premise hT of five_at_first, at the lot's own job at the first chain's proximity test
(jobL), under the head, from "Bk is the maker's book".** The door, the rows' data, the readers and
the closing are letters. -/
theorem hT_head_L {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) {W₀ Rc Xi Tr X : Type}
    (door : Local W₀ Rc Xi Tr → Front X → T12) (Dr : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) :
    tiesB Bk (jobL (H2U.p12OfMade Zp.made) door Dr readers closing pl).p.place
      (jobL (H2U.p12OfMade Zp.made) door Dr readers closing pl).members.length = true := by
  have hpl : (jobL (H2U.p12OfMade Zp.made) door Dr readers closing pl).p.place = placeL := by
    show (H2U.p12OfMade Zp.made).place = placeL
    rw [numbersL_at_head h]
    exact p12At_place _ _
  have hm : (jobL (H2U.p12OfMade Zp.made) door Dr readers closing pl).members.length = 185 :=
    membersL_185 h hG hf
  rw [hpl, hm]
  exact ties_at_laid_L h.scope h.laid hB

end AtFullSide.K12

#print axioms AtFullSide.K12.membersL_185
#print axioms AtFullSide.K12.hT_head_L
