-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/LaysAtOpening.lean: the closed Script of the first chain (firstScriptAt,
AtFullSide/K1/FirstScript.lean) lays the filling of the matrices at segment 0: the form LaysFilling
(Honest/K5/Law/LaysFilling.lean) at the seat of the first segment's opening. The fellow of
AtFullSide/K1/LaysAtSwitches.lean, which has the segments 1 to 24.

  1  firstOkW   a closed fact at the written plan, by evaluation in Lean's kernel: each message of moment 0 of
     link 0 stands in the opening's sending, and the plan's numbering at its seat gives the plan's number
     of that message
  2  opening_lays   THE STEP, general in the Script: at one message of the opening
  3  laysFilling_opening   THE END: LaysFilling at firstScriptAt at segment 0. NO HYPOTHESIS BUT THE HEAD, THE
     MAKER's RETURN AND A BOUND ON N

Why nothing is left open here. The opening is K1's own sending: that its texts answer at this book is the
field coins of joinFit_first (msgTxt_answers, Honest/K1/LotsLaid.lean).

Limits. The head h and the return hA are hypotheses. N is at least the number of rounds in front of member
number 2: K1's tie speaks from there on. At the sizes Sz.ref alone. At Vd := fun _ => False the field lays
says nothing. It says what the Script's messages hold as a function of the readers of the input: nothing on
what the readers hold. Main rows alone. This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.LaysAtSwitches
import Johnson.Desc.ProofFile.Honest.K1.FirstOffPad
import Johnson.Desc.ProofFile.Honest.K1.DataLaw
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead

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
open Johnson.Prover.Send (shapeAt Rows)
open P5J (AtMgA CellsM TS)
open P5T (seatsAllFull)
open ProofFile.Honest.FirstThread

/-! ## 1 A closed fact -/

set_option maxRecDepth 1000000 in
/-- **At the written plan each message of moment 0 of link 0 stands in the opening's sending, under the
plan's number.** Two controls: there are three; at the numbering shifted by one the test fails. -/
theorem firstOkW :
    ((List.range (momentZero proofSizedFull.request 0)).all fun n =>
      decide (n < parGF.sent.size) && (msgNo proofSizedFull.request 0 0 n).any fun m =>
        decide (P5T.arrOf seatsAllFull (seatOfMsg parGF 0 n).1 (seatOfMsg parGF 0 n).2 =
          P5T.numOfPlan seatsAllFull 0 m)) = true ∧
      momentZero proofSizedFull.request 0 = 3 ∧
      ((List.range (momentZero proofSizedFull.request 0)).any fun n =>
        (msgNo proofSizedFull.request 0 0 n).any fun m =>
          decide (P5T.arrOf seatsAllFull (seatOfMsg parGF 0 n).1 (seatOfMsg parGF 0 n).2 + 1 =
            P5T.numOfPlan seatsAllFull 0 m)) = false := by
  decide +kernel

/-! ## 2 The step -/

/-- **AT ONE MESSAGE OF THE OPENING: THE SCRIPT's MESSAGE HOLDS WHAT THE OPENING's FILLING ANSWERS.** General
in the Script. hm: the Script holds the job's text at the number num. hC: the book's count at the part's
address is the part's due. -/
theorem opening_lays {Bk : ProverCoinCounts} {Wl Cells' Tok' : Type} (Q : Script Bk Wl Cells' Tok' MsgT)
    (Vd : Wl → Prop) (N : Nat) (S : Sz) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (wit : Wl → PlaceIn ProofFile.Inst) (num fx n : Nat)
    (hm : OwnMsgs Q Vd N num fx (msgTxt 0 wit (jobTwoAt S Z G) () n))
    (hC : dueAt (Bk.rowsOf 0) ⟨(jobTwoAt S Z G).P.place, 0⟩ =
      dueR (jobTwoAt S Z G).P (jobTwoAt S Z G).ride)
    (hlen : G.first.codes.lengthsOk = true)
    (k : Coins Bk) (v : Wl) (hd : List Fmt.Drawn) (hv : Vd v) (hN : N ≤ hd.length)
    (row place : Nat) (y : Cb.Gl.F ⊕ Cb.Gl.E)
    (hask : (firstFill S G.first).ask (wit v).R hd ⟨firstAddr, n⟩ row place = .ok (some y)) :
    Q.msg num k v (hd.take (Q.fixedMsg num)) false row place = asE (some y) := by
  obtain ⟨hl, hy⟩ := ask_gives hask
  obtain ⟨hr, hj, hp, ha⟩ := first_lays_room S G.first (K1.gpOf Z) hlen n row place hl
  obtain ⟨x, hx⟩ := entry_inl S G.first.codes G.first.shape G.first.layout
    (firstSeat G.first.shape 0) (fun _ => 0) (wit v).R [] ⟨firstAddr, n⟩ row place
  have hyx : y = .inl x := hy.trans hx
  have hdat : (jobTwoAt S Z G).data (wit v) { heard := hd.take fx, own := (), seen := .bare [] } n
      row place = some (.inl x) := by
    show (lotData S Z G (wit v).x).forSend (wit v).R firstAddr (hd.take fx) n row place = _
    rw [data_first]
    show (firstFill S G.first).at_ (wit v).R (hd.take fx) ⟨firstAddr, n⟩ row place = _
    unfold RowData.at_
    rw [if_pos hl]
    exact congrArg some hx
  obtain ⟨y', hy'⟩ := msgTxt_answers hC wit () n k v (hd.take fx) false row place
  rw [hm k v hd hv hN false row place y' hy', hyx]
  unfold msgTxt at hy'
  obtain ⟨c, -, e⟩ := Option.map_eq_some_iff.1 hy'
  rw [← e]
  show (rowsR (jobTwoAt S Z G).P (jobTwoAt S Z G).ride
    ((jobTwoAt S Z G).data (wit v) { heard := hd.take fx, own := (), seen := .bare [] }) c n).main
    ((shapeAt (jobTwoAt S Z G).P n).mainDeg == 3) row place = _
  unfold Rows.main
  by_cases h3 : ((shapeAt (jobTwoAt S Z G).P n).mainDeg == 3) = true
  · rw [if_pos h3, main_data_e (jobTwoAt S Z G).P (jobTwoAt S Z G).ride _ c n row place h3 hr hj ha hp,
      hdat]
    exact (K5.asE_inl x).symm
  · rw [if_neg h3, main_data_f (jobTwoAt S Z G).P (jobTwoAt S Z G).ride _ c n row place
      (Bool.eq_false_iff.2 h3) hr hj ha hp, hdat]
    exact (K5.asE_inl x).symm

/-! ## 3 The end -/

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE CLOSED SCRIPT LAYS THE FILLING OF THE MATRICES AT SEGMENT 0**, at the seat of the opening, at "no
challenge has been heard", at the filling's own readers, at every Vd, from the rounds in front of member
number 2 on. -/
theorem laysFilling_opening (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (Vd : LocB W₀ → Prop) {N : Nat} (hN0 : 0 + roundsTo cF.blocksInOrder 2 ≤ N) :
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
  have hm := (tie_k1_first h hA Vd hmem).1 Ad.msg hn
  exact opening_lays (firstScriptAt I Sz.ref Op A cF) Vd N Sz.ref A.Z A.G (witB I A.Z) _ _ Ad.msg
    (fun k w hd hw hN' => hm k w hd hw (Nat.le_trans hN0 hN'))
    ((joinFit_first h hA).coins _ hmem) (by rw [cG]; exact lengthsW) k v hd hv hN row place y hask

end ProofFile.Honest.K1

end

#print axioms ProofFile.Honest.K1.firstOkW
#print axioms ProofFile.Honest.K1.opening_lays
#print axioms ProofFile.Honest.K1.laysFilling_opening
