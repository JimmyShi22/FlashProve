-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/LaterAtPlanNumbers.lean: at the closed Script of the first chain (firstScriptAt,
AtFullSide/K1/FirstScript.lean), each message of moment 1 or 2 of each of the 25 links is, UNDER THE PLAN's OWN
NUMBER OF THAT MESSAGE (P5J.At.num), the own whole text of K1's later job at that link and moment. The fellow of
AtFullSide/K1/OwnAtPlanNumbers.lean, which has moment 0.

  1  laterOkW   a closed fact at the written plan, by evaluation in Lean's kernel: at each link and each of the
     moments 1 and 2, each message m of that moment, of rank n among its moment's messages, stands as member n
     of the later place's sending, and the plan's numbering at its seat gives the plan's number of (link, m)
  2  ownMsgs_later_num   OwnMsgs at the number P5J.At.num A.Z l m and the job's text of message n, at every Vd, N

The message is named as a seat of an array names it: OnBytes.HonestTrace.inSending of the link and m is the
moment and the rank (Johnson/HonestTrace/SeatOf.lean; seat_text, Honest/K1/LaterOffPad.lean).

Why. k1Num_fifty (Honest/K1/Law/K1NumAtHead.lean) says that K1's number at a later message is the plan's number
of SOME message of the link. Whoever reads the witness by the plan's number of the seat's own message needs
which.

Limits. The head h and the return hA are hypotheses. Where a text answers nothing this says nothing: K1's
texts answer at this book (msgTxt_answers, from joinFit_first's field coins). This file proves nothing about
completeness, soundness or hiding.
-/
import AtFullSide.K1.LaysAtEveryList
import AtFullSide.K1.OwnAtPlanNumbers
import Johnson.Desc.ProofFile.Honest.K1.Law.PiecesAndPort
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.K1 (seatOfMsg)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (inSending)
open P5J (AtMgA CellsM TS)
open P5T (seatsAllFull)
open ProofFile.Honest.FirstThread

/-- The public test at link l, the moment of d, and message m of the link. bend: added to K1's number, for a
control. -/
def laterMsgOk (bend l : Nat) (d : Bool) (m : Nat) : Bool :=
  match inSending (proofSizedFull.request.link.getD l default) m with
  | some (t, n) =>
    t != cond d 2 1 ||
      (decide (n < (K1.placeL l d).sent.size) &&
        decide (P5T.arrOf seatsAllFull (seatOfMsg (K1.placeL l d) (K1.baseL3 l d) n).1
          (seatOfMsg (K1.placeL l d) (K1.baseL3 l d) n).2 + bend = P5T.numOfPlan seatsAllFull l m))
  | none => true

/-- How many messages of link l are of the moment of d. -/
def laterCount (l : Nat) (d : Bool) : Nat :=
  ((proofSizedFull.request.link.getD l default).messages.filter fun M => M.moment == cond d 2 1).length

set_option maxRecDepth 1000000 in
/-- **The test passes at all 25 links, both moments, all messages.** Two controls: each link has a message
of each of the two moments; with K1's number bent by one the test fails at every link and moment. -/
theorem laterOkW :
    ((List.range 25).all fun l => [false, true].all fun d =>
      (List.range (proofSizedFull.request.link.getD l default).messages.length).all
        (laterMsgOk 0 l d)) = true ∧
      ((List.range 25).all fun l => [false, true].all fun d => decide (0 < laterCount l d)) = true ∧
      ((List.range 25).any fun l => [false, true].any fun d =>
        (List.range (proofSizedFull.request.link.getD l default).messages.length).all
          (laterMsgOk 1 l d)) = false := by
  decide +kernel

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **A LINK's MESSAGE OF MOMENT 1 OR 2, UNDER THE PLAN's NUMBER, IS K1's LATER JOB's OWN TEXT.** d = false: the
link's reads, moment 1; d = true: its digits, moment 2. hin: message m of link l is of that moment, of rank n
among the moment's messages. At every Vd and N. -/
theorem ownMsgs_later_num (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat) {l : Nat} (hl : l < 25) (d : Bool) {m n : Nat}
    (hin : inSending (A.G.first.shape.link.getD l default) m = some (cond d 2 1, n)) :
    OwnMsgs (firstScriptAt I S Op A cF) Vd N (P5J.At.num A.Z l m)
      (0 + roundsTo cF.blocksInOrder (K1.noL l d)) (msgTxt 0 (witB I A.Z) (jobLaterAt S A.Z A.G l d) () n) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hS : P5J.At.pseatsAll A.Z = seatsAllFull := pseatsAll_written h
  rw [shape_at_base h hA] at hin
  have hm : m < (proofSizedFull.request.link.getD l default).messages.length := by
    unfold inSending at hin
    obtain ⟨M, hM, -⟩ := Option.map_eq_some_iff.1 hin
    exact (List.getElem?_eq_some_iff.1 hM).1
  have hok := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 laterOkW.1 l
    (List.mem_range.2 hl)) d (by cases d <;> simp)) m (List.mem_range.2 hm)
  unfold laterMsgOk at hok
  rw [hin] at hok
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    Nat.add_zero] at hok
  obtain ⟨g1, g2⟩ := hok
  have eL : (jobLaterAt S A.Z A.G l d).P = K1.parL A.Z Bs.G₀ l d := by
    rw [parL_later, ← eG]
    rfl
  have eP : (jobLaterAt S A.Z A.G l d).P = K1.placeL l d := eL.trans (parL_written h O l d)
  have hn : n < (jobLaterAt S A.Z A.G l d).P.sent.size := by rw [eP]; exact g1
  have hnum : P5J.At.arr A.Z (seatAtMember cF.blocksInOrder (K1.noL l d) (jobLaterAt S A.Z A.G l d).P n).1
      (seatAtMember cF.blocksInOrder (K1.noL l d) (jobLaterAt S A.Z A.G l d).P n).2 = P5J.At.num A.Z l m := by
    rw [eL, seat_fifty_written h O hl d n]
    show P5T.arrOf (P5J.At.pseatsAll A.Z) _ _ = P5T.numOfPlan (P5J.At.pseatsAll A.Z) l m
    rw [hS]; exact g2
  rw [← hnum]
  exact ownMsgs_k1_any h hA Vd N
    (y := (K1.noL l d, jobLaterAt S A.Z A.G l d))
    (mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inr ⟨l, hl, d, rfl⟩)))) hn

end ProofFile.Honest.K1

end

#print axioms ProofFile.Honest.K1.laterOkW
#print axioms ProofFile.Honest.K1.ownMsgs_later_num
