-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingHead.lean: the letter of the first chain's closing
proximity test (`LetterAtL`, ClosingAtL.lean) filled at the library's own thread (`lettersHead`,
Honest/Thread/FirstHead.lean), under the head, at the job `jobL` at the filled door. One premise
stays: that the prover's side at the test's place is that job's half.

  `member_354`      member 354 of the first chain's flat list is the test at its two guards
  `ps_354`          number 354 of the written places is the test's
  `stages_L_shape`  the written stages: two at least, and the first is as the test's law asks
  `letterAtL_head`  the letter, at `lettersHead`

By what. `IM.back_of`, `IM.back_numbers`: the member, in the text of `firstCore`
(Johnson/Loose/H2K12/FirstSeatForm.lean); `p12OfMade_place` (Johnson/Loose/H2K12/SitsInPure.lean); `seatOf_entry` (ClosingSeat.lean);
`front_is_take_L`, `keepsInFront_L` (K12/Blind/KeepsAtFinish.lean): what stands in front of it;
`flatL_at_head` (K12/AtProof/LotAtDoor.lean): the door; `p12_at_head`
(Johnson/AtFull/Shape/TestNumbersAtHead.lean): the test's numbers are the written `piLFull`.

Hypotheses. h: the head. hh: the side that the prover lists at the test's place is `proverSideOfProximityTest` of the
job. `halves_head_L` (AtFullSide/K12/FitsAtHeadL.lean) says that the lot has that one half; that the
term's list holds the lot's half at that place, read through, is the crossing's.

Limits.
- Full size, the format's own hash alone. That the head has a member is shown in scope, where the
reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three
hold together, at two named sets of public files, in a side library.
- The job's `D`, `readers`, `closing` and `pl` are letters here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingAtL
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingSeat
import Johnson.Desc.ProofFile.Honest.K12.Blind.KeepsAtFinish
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotAtDoor
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.AtFull.Shape.TestNumbersAtHead
import Johnson.IMR.BackSeat
import Johnson.Loose.H2K12.SitsInPure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open H2K.Pub (sgOf)
open H2K.Member (piLFull)
open H2K.JointK (firstEntry firstCore outCore)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K12.AtProof (jobL doorAtL startL placeL flatL_at_head idleT12)
open ProofFile.Honest.K12.Blind (front_is_take_L keepsInFront_L)
open P5J (AtMg AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Member 354 is the test at its two guards.** -/
theorem member_354 (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) :
    ∃ nm, cF.blocksInOrder[354]? =
      some (firstEntry ProofFile.sameReply (firstCore (H2U.p12OfMade Zp.made) nm)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ⟨b, b', eb, -, rfl, la⟩, -, -⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 1 b eb
  have la' : b = IM.seatedAs ProofFile.sameReply _ b.name _ := la
  generalize b.name = nm at la'
  subst la'
  exact ⟨nm, q⟩

theorem ps_354 : P5J.At.ps[354]? = some placeL := by
  decide +kernel

theorem stages_L_shape : ∃ s u rest, piLFull.nums.stages = s :: u :: rest ∧
    s.k = (sgOf s).h + (sgOf s).g := by
  have hl : 2 ≤ piLFull.nums.stages.length := by decide +kernel
  have hk : (piLFull.nums.stages.headD default).k =
      (sgOf (piLFull.nums.stages.headD default)).h +
        (sgOf (piLFull.nums.stages.headD default)).g := by decide +kernel
  cases hs : piLFull.nums.stages with
  | nil =>
    rw [hs] at hl
    cases hl
  | cons s l =>
    cases l with
    | nil =>
      rw [hs] at hl
      simp at hl
    | cons u rest =>
      rw [hs] at hk
      exact ⟨s, u, rest, rfl, hk⟩

/-- **The letter, at the library's own thread.** -/
theorem letterAtL_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → VerifiableInference.Desc.Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (hh : (H.first.find? fun g => g.place == (H2U.p12OfMade Zp.made).place) =
      some (proverSideOfProximityTest (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl))) :
    ∃ blk pre t, cF.blocksInOrder[354]? = some blk ∧
      LetterAtL (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 354
        (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)
        (outCore ProofFile.sameReply) (startL Zp) idleT12 blk pre t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨nm, hm⟩ := member_354 h
  have hl : 354 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hm).1
  have hd : cF.blocksInOrder.drop 354 =
      firstEntry ProofFile.sameReply (firstCore (H2U.p12OfMade Zp.made) nm) :: cF.blocksInOrder.drop 355 := by
    rw [List.drop_eq_getElem_cons hl]
    congr 1
    exact Option.some.inj ((List.getElem?_eq_getElem hl).symm.trans hm)
  have hw := front_is_take_L h.scope h.reads O
  have hbp : (firstEntry ProofFile.sameReply (firstCore (H2U.p12OfMade Zp.made) nm) :
      Block S ProofFile.Cl).place = placeL := rfl
  obtain ⟨s, u, rest, hs, hk⟩ := stages_L_shape
  refine ⟨_, cF.blocksInOrder.take 354, cF.blocksInOrder.drop 355, hm, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ps_354, fun _ => rfl, ?_,
    seatOf_entry (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) nm
      (H2K.JointK.p12OfMade_place Zp), hh, s, u, rest, ?_, hk⟩
  · show cF.blocksInOrder = _
    rw [← hd, List.take_append_drop]
  · rw [List.length_take]
    omega
  · intro y hy e
    rw [← hw] at hy
    have hne := List.mem_takeWhile_imp hy
    rw [e, hbp] at hne
    simp at hne
  · intro y hy
    rw [← hw] at hy
    exact keepsInFront_L h.scope h.reads O y hy
  · show doorAtL Zp = ProofFile.Honest.K12.Blind.doorL cF.blocksInOrder (startL Zp) placeL idleT12
    unfold doorAtL
    rw [flatL_at_head h.toAtMg]
  · show (H2U.p12OfMade Zp.made).nums.stages = _
    rw [Johnson.AtFull.Shape.p12_at_head h.toAtMg]
    exact hs

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.member_354
#print axioms ProofFile.Honest.K12.ps_354
#print axioms ProofFile.Honest.K12.stages_L_shape
#print axioms ProofFile.Honest.K12.letterAtL_head
