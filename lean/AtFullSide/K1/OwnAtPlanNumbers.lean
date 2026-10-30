-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/OwnAtPlanNumbers.lean: at the closed Script of the first chain (firstScriptAt,
AtFullSide/K1/FirstScript.lean), each message of moment 0 of each of the 25 links is, UNDER THE PLAN's OWN NUMBER
OF THAT MESSAGE (P5J.At.num), its sender's own whole text: the opening's at link 0, the code switch's at the
links 1 to 24.

  1  switch_into_first   into each link from 1 to 24 a place of the code switch leads
  2  ownMsgs_switch_num   at a place p of the code switch and the i-th message m of moment 0 of its link:
     OwnMsgs at the number P5J.At.num A.Z p.link m and the switch's text of message 1 + kept + i
  3  ownMsgs_opening_num   at the n-th message m of moment 0 of link 0: OwnMsgs at the number
     P5J.At.num A.Z 0 m and the opening's job's text of message n

What for. The spenders of a link's mask row and of its matrices read the witness by the plan's number of the
link's message. tie_k1_first and ownMsgs_switch_first bear the senders' own numbers; here the two numberings
are joined, by the closed tests of LaysAtSwitches.lean and LaysAtOpening.lean and the code switch's authors'
ownNum_at_head. Which message of a link has the mask row is of moment 0 at the written shape:
maskRow_momentW (MomentZeroWritten.lean).

Limits. The head h and the return hA are hypotheses. Where a text answers nothing these say nothing. At link 0
from the rounds in front of member number 2 on. This file proves nothing about completeness, soundness or
hiding.
-/
import AtFullSide.K1.LaysAtOpening

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.K1 (parGF seatOfMsg)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open P5T (seatsAllFull)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2.Law (placesW)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The ground's shape is the written one. -/
theorem shape_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    A.G.first.shape = proofSizedFull.request := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [eG, O.first]
  exact (H2K5.Door.made_row_gives (H2K5.Door.pins_at_head h.toAtMg).1).1.2.2.1

/-- **Into each link from 1 to 24 a place of the code switch leads.** -/
theorem switch_into_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {l : Nat} (h1 : 1 ≤ l) (h25 : l < 25) : ∃ p ∈ K2.switchPlaces A.Z A.G, p.link = l := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hP : K2.switchPlaces A.Z A.G = placesW := by
    rw [eG]; exact K2.Law.places_at_head h.toAtMg O
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  obtain ⟨p, hp, e⟩ := List.any_eq_true.1
    (List.all_eq_true.1 linksW.1 l' (List.mem_range.2 (by omega)))
  exact ⟨p, hP ▸ hp, beq_iff_eq.1 e⟩

/-- **A LINK's MESSAGE OF MOMENT 0, UNDER THE PLAN's NUMBER, IS THE SWITCH's OWN TEXT**, at the links 1 to 24.
At every Vd and N. At the finish's place, which leads behind the last link, no message is found and the law
says nothing. -/
theorem ownMsgs_switch_num (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat) {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces A.Z A.G)
    {i m : Nat} (hno : msgNo A.G.first.shape p.link 0 i = some m) :
    OwnMsgs (firstScriptAt I S Op A cF) Vd N (P5J.At.num A.Z p.link m)
      (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place))
      (K2.switchMsgTxt 0 (widerRows S A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) p
        (1 + p.sizes.kept.length + i)) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hP : K2.switchPlaces A.Z A.G = placesW := by
    rw [eG]; exact K2.Law.places_at_head h.toAtMg O
  have hS : P5J.At.pseatsAll A.Z = seatsAllFull := K2.Law.pseatsAll_at_head h.toAtMg
  have hok := List.all_eq_true.1 placesOkW.1 p (hP ▸ hp)
  unfold placeOk at hok
  rw [Bool.and_eq_true] at hok
  rw [shape_at_base h hA] at hno
  obtain ⟨g1, g2, g3, -⟩ := ownMsgOk_gives
    (List.all_eq_true.1 hok.2 _ (List.mem_range.2 (rank_lt hno))) hno
  rw [← K2.Law.ownNum_at_head h.toAtMg O p (eG ▸ hp) _ m g1 (by rw [hS]; exact g3)]
  exact ownMsgs_switch_first h hA Vd N hp g1 g2

/-- **A MESSAGE OF MOMENT 0 OF LINK 0, UNDER THE PLAN's NUMBER, IS THE OPENING's JOB's OWN TEXT.** At every
Vd, from the rounds in front of member number 2 on. -/
theorem ownMsgs_opening_num (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) {n m : Nat} (hno : msgNo A.G.first.shape 0 0 n = some m) :
    OwnMsgs (firstScriptAt I S Op A cF) Vd (0 + roundsTo cF.blocksInOrder 2) (P5J.At.num A.Z 0 m)
      (0 + roundsTo cF.blocksInOrder 2) (msgTxt 0 (witB I A.Z) (jobTwoAt S A.Z A.G) () n) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hS : P5J.At.pseatsAll A.Z = seatsAllFull := pseatsAll_written h
  have hmem : ((2, jobTwoAt S A.Z A.G) : Nat × SendJob (PlaceIn ProofFile.Inst) Unit) ∈
      k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G) :=
    mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inl rfl)))
  rw [shape_at_base h hA] at hno
  have hok := List.all_eq_true.1 firstOkW.1 n (List.mem_range.2 (rank_lt hno))
  rw [hno] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_some] at hok
  obtain ⟨g1, g2⟩ := hok
  have eP : K1.firstPar A.G.first (K1.gpOf A.Z) = parGF := by
    rw [eG]; exact K1.eG_atAll h O (K1.pin1_atAll h)
  have hn : n < (jobTwoAt S A.Z A.G).P.sent.size := by
    show n < (K1.firstPar A.G.first (K1.gpOf A.Z)).sent.size
    rw [eP]; exact g1
  have hnum : P5J.At.arr A.Z (seatAtMember cF.blocksInOrder 2 (jobTwoAt S A.Z A.G).P n).1
      (seatAtMember cF.blocksInOrder 2 (jobTwoAt S A.Z A.G).P n).2 = P5J.At.num A.Z 0 m := by
    have e2 : seatAtMember cF.blocksInOrder 2 (jobTwoAt S A.Z A.G).P n = seatOfMsg parGF 0 n := by
      show seatAtMember cF.blocksInOrder 2 (K1.firstPar A.G.first (K1.gpOf A.Z)) n = _
      rw [eG]; exact seat_two_written h O n
    rw [e2]
    show P5T.arrOf (P5J.At.pseatsAll A.Z) _ _ = P5T.numOfPlan (P5J.At.pseatsAll A.Z) 0 m
    rw [hS]; exact g2
  rw [← hnum]
  exact (tie_k1_first h hA Vd hmem).1 n hn

end ProofFile.Honest.K1

end

#print axioms ProofFile.Honest.K1.shape_at_base
#print axioms ProofFile.Honest.K1.switch_into_first
#print axioms ProofFile.Honest.K1.ownMsgs_switch_num
#print axioms ProofFile.Honest.K1.ownMsgs_opening_num
