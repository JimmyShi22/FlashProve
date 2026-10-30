-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/LaysAtEveryList.lean: at the closed Script of the first chain (firstScriptAt,
AtFullSide/K1/FirstScript.lean) the matrices' entries are the same AT EVERY LIST OF CHALLENGES, the empty one too.

  1  ownMsgs_k1_any   each message of each of K1's 52 members is the job's own text, at every N: tie_k1_first
     without its bound
  2  laysFilling_opening_any   LaysFilling at segment 0 at every N: laysFilling_opening without its bound
  3  msg_at_laid   from LaysFilling at N := 0, general in the Script: at each element that the layout lays of an
     array that the filling of the matrices serves, the Script's message, as the witness reads it, holds the
     filling's value at every list of challenges; the value names no challenge

What for. A message's field fixedMsg at a Script laid by lots is the greatest fx of its lots, which is the
number of challenges in front of the sender: it is 0 only where no round stands in front of the sender. So
"fixedMsg = 0 at every seat" is not to be had at this Script. What holds in its place is 3: the witness's
entry at a seat of a matrix is one value at all lists.

Limits. The head h and the return hA are hypotheses. The Script's message is read as the witness reads it:
at the list cut at fixedMsg (Script.wit, Honest/Thread/First.lean). At the segments 1 to 24 LaysFilling stands
under hLent, hClose and hPub (AtFullSide/K1/LaysAtSwitches.lean). At the sizes Sz.ref. This file proves nothing
about completeness, soundness or hiding.
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
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA CellsM TS)
open P5T (seatsAllFull)
open ProofFile.Honest.FirstThread

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **EACH MESSAGE OF EACH OF K1's 52 MEMBERS IS THE JOB's OWN TEXT, AT EVERY N.** -/
theorem ownMsgs_k1_any {S : Sz} (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat) {y : Nat × SendJob (PlaceIn ProofFile.Inst) Unit}
    (hy : y ∈ k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G)) {n : Nat}
    (hn : n < y.2.P.sent.size) :
    OwnMsgs (firstScriptAt I S Op A cF) Vd N
      (P5J.At.arr A.Z (seatAtMember cF.blocksInOrder y.1 y.2.P n).1 (seatAtMember cF.blocksInOrder y.1 y.2.P n).2)
      (0 + roundsTo cF.blocksInOrder y.1) (msgTxt 0 (witB I A.Z) y.2 () n) := by
  have hL : (⟨P5J.At.arr A.Z (seatAtMember cF.blocksInOrder y.1 y.2.P n).1 (seatAtMember cF.blocksInOrder y.1 y.2.P n).2,
      0 + roundsTo cF.blocksInOrder y.1, msgTxt 0 (witB I A.Z) y.2 () n⟩ : MsgLot A.B (LocB W₀)) ∈
      joinMl cF.blocksInOrder 0 (P5J.At.arr A.Z) (witB I A.Z) ()
        (k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G))
        (otherSendersAt I S A cF) :=
    List.mem_append.2 (.inl (mem_k1MsgLots hy (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)))
  exact ofLots_ownMsgs_all cF.blocksInOrder 0 (cellsB I A.Z) tokB _ _ _ (joinFit_first h hA).msgs Vd N _ hL

/-- **THE CLOSED SCRIPT LAYS THE FILLING OF THE MATRICES AT SEGMENT 0, AT EVERY N.** -/
theorem laysFilling_opening_any (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat) :
    K5.LaysFilling h (firstScriptAt I Sz.ref Op A cF) Vd N (readersB I A.Z)
      (firstSeat h.𝔇.sent.shape 0) (fun _ => 0) 0 := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have eF : A.G.first = A.Z.first := by rw [eG]; exact O.first
  obtain ⟨f1, -, f3, -, -, f6⟩ :=
    (H2K5.Door.made_row_gives (H2K5.Door.pins_at_head h.toAtMg).1).1
  have c𝔇 : h.𝔇.sent.codes = proofSizedFull.codes := f1
  have s𝔇 : h.𝔇.sent.shape = proofSizedFull.request := f3
  have l𝔇 : h.𝔇.sent.layout = Johnson.G.layoutFull := f6
  have cG : A.G.first.codes = proofSizedFull.codes := by rw [eF]; exact f1
  have sG : A.G.first.shape = proofSizedFull.request := by rw [eF]; exact f3
  have lG : A.G.first.layout = Johnson.G.layoutFull := by rw [eF]; exact f6
  have hS : P5J.At.pseatsAll A.Z = seatsAllFull := pseatsAll_written h
  have hmem : ((2, jobTwoAt Sz.ref A.Z A.G) : Nat × SendJob (PlaceIn ProofFile.Inst) Unit) ∈
      k1MembersW (jobTwoAt Sz.ref A.Z A.G) (jobLaterAt Sz.ref A.Z A.G) (jobWAt Op A.Z A.G) :=
    mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inl rfl)))
  refine ⟨fun As Ar hl hAr hz => K5.reach_firstSeat h N hl hAr hz, ?_⟩
  intro k v hd hv hN Ad m hseat row place y hask
  rw [c𝔇, s𝔇, l𝔇, ← cG, ← sG, ← lG] at hask
  rw [s𝔇] at hseat
  obtain ⟨a1, -, -, -⟩ := momentSeat_says hseat
  have hno := momentSeat_no hseat
  rw [Nat.sub_zero] at hno
  have eAd : Ad = ⟨firstAddr, Ad.msg⟩ := by
    obtain ⟨sd, ms⟩ := Ad
    have b1 : sd = firstAddr := a1
    rw [b1]
  have hok := List.all_eq_true.1 firstOkW.1 Ad.msg (List.mem_range.2 (rank_lt hno))
  rw [hno] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_some] at hok
  obtain ⟨g1, g2⟩ := hok
  have eP : K1.firstPar A.G.first (K1.gpOf A.Z) = parGF := by
    rw [eG]; exact K1.eG_atAll h O (K1.pin1_atAll h)
  have hn : Ad.msg < (jobTwoAt Sz.ref A.Z A.G).P.sent.size := by
    show Ad.msg < (K1.firstPar A.G.first (K1.gpOf A.Z)).sent.size
    rw [eP]; exact g1
  have hnum : P5J.At.arr A.Z
      (seatAtMember cF.blocksInOrder 2 (jobTwoAt Sz.ref A.Z A.G).P Ad.msg).1
      (seatAtMember cF.blocksInOrder 2 (jobTwoAt Sz.ref A.Z A.G).P Ad.msg).2 = P5J.At.num A.Z 0 m := by
    have e2 : seatAtMember cF.blocksInOrder 2 (jobTwoAt Sz.ref A.Z A.G).P Ad.msg = seatOfMsg parGF 0 Ad.msg := by
      show seatAtMember cF.blocksInOrder 2 (K1.firstPar A.G.first (K1.gpOf A.Z)) Ad.msg = _
      rw [eG]; exact seat_two_written h O Ad.msg
    rw [e2]
    show P5T.arrOf (P5J.At.pseatsAll A.Z) _ _ = P5T.numOfPlan (P5J.At.pseatsAll A.Z) 0 m
    rw [hS]; exact g2
  rw [← hnum]
  rw [eAd] at hask
  have hm := ownMsgs_k1_any h hA Vd N hmem hn
  exact opening_lays (firstScriptAt I Sz.ref Op A cF) Vd N Sz.ref A.Z A.G (witB I A.Z) _ _ Ad.msg
    hm
    ((joinFit_first h hA).coins _ hmem) (by rw [cG]; exact lengthsW) k v hd hv hN row place y hask


/-- **AT A LAID ELEMENT OF A MATRIX's ARRAY THE WITNESS's ENTRY IS ONE VALUE AT ALL LISTS OF CHALLENGES.** General
in the Script. L: LaysFilling at N := 0. The hypotheses on the array are msg_of_lays' own
(Honest/K5/Law/LaysFilling.lean). -/
theorem msg_at_laid {Bk : ProverCoinCounts} {Rc Tr : Type} {Zp : ProofFile.Pub}
    {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : MsgAddr → Option (Nat × Nat)} {heard : MsgAddr → Nat} {l : Nat}
    (L : K5.LaysFilling h Q Vd 0 rd seat heard l) {n : String} {Ar : OnBytes.Params.ReqArray}
    (hAr : VerifiableInference.Desc.arrayOf h.𝔇.sent.layout l n = some Ar) {i' c : Nat} {p : Nat × Nat}
    (hp : VerifiableInference.Desc.laidAt Ar i' c = some p) {z : Nat × Nat}
    (hz : (cellsVals Sz.ref).size l Ar.name = some z) (hi : i' < z.1) (hc : c < z.2)
    (k : Coins Bk) {v : Local W₀ Rc ProofFile.Inst Tr} (hv : Vd v) (hd : List Fmt.Drawn) :
    Q.msg (P5J.At.num Zp l Ar.message) k v (hd.take (Q.fixedMsg (P5J.At.num Zp l Ar.message))) false
        p.1 p.2 =
      asE (some ((cellsVals Sz.ref).val (rd v) [] l Ar.name i' c)) := by
  obtain ⟨hd', e⟩ := K5.msg_of_lays L hAr hp hz hi hc k hv (hd := hd) (Nat.zero_le _)
  exact e

end ProofFile.Honest.K1

end

#print axioms ProofFile.Honest.K1.ownMsgs_k1_any
#print axioms ProofFile.Honest.K1.laysFilling_opening_any
#print axioms ProofFile.Honest.K1.msg_at_laid
