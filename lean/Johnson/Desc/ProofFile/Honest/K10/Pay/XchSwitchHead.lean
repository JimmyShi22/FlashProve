-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchSwitchHead.lean: the closing of a segment (K10): THE TWO RECORDS OF THE CODE SWITCH
(`TieBySwitch`, Pay/XchTieBySwitch.lean; `FreshBySwitch`, Pay/XchFreshField.lean) UNDER THE HEAD, at the first chain's thread, at
each segment into which a code switch leads (1 to 24): every public field and every clause at a stand that this folder pays is
paid; what is left stands as named premises.

  **`tieBySwitch_head`**, **`freshBySwitch_head`**   the records, at: the thread's own valid inputs; p the written place of link l; the
      number fxAt cF p; the seats seatSw Zp p. LEFT AS PREMISES:
      on the script   msg, pad: at every message of the switch's sending: its text off the pad, its pad's text
      on the book     book, bookFront (tie) · book (fresh) · hH: the switch's part is handed its coins at every run's coins
      on the switch   hV: its rows are laid, at every valid input and every list of challenges
      on the filling  hD1: the data of an own message of a segment in front read no more challenges than fxAt · hzero: the data of a
                      switch's own message, the last message apart, read none
      public          hS, hP: the segments are the written ones; p is a place of the kind · hvars: the switch's count of the next
                      fold's row variables is the closing's · hN: N ≤ fxAt

By this folder's XchPublic, XchSwitchPub, XchSeatsAt, XchMaskAt, XchOwnAt, XchStand; `thr_reach` (Honest/Thread/ReachFacts.lean).

Limits. The head is a premise. That a run stands at the border is not shown. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieBySwitch
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshField
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSwitchPub
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchMaskAt
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchOwnAt
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (SwitchPlace fromE dueBefore messageDue switchSent switchFresh switchPlaces segmentsOf handed
  switchRowsLaid switchMsgOff switchPadTxt lotClosingAt)
open ProofFile.Honest.K2.Law (segsW placesW)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. The option turns off one early look at a notation's text, which has no case for a
-- field access; it loosens nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- At a stand in front of a closing: the state is reached and has not failed. -/
theorem stand_reached {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {l : Nat}
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l pw Qc blk)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn} {s' : TS}
    (St : StepAt 𝕋 Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s') :
    Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (m.st.input.x.pub, s) ∧
      s.failed = none ∧ l < 25 ∧ Qc.link = l := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hT := St.thr.1
  have hr := thr_reach h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) hT
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hP, -, -, -, -⟩ := hT'
  exact ⟨hr, Option.isNone_iff_eq_none.1 hP.1, link_lt h hlt,
    (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1⟩

/-- **The record on the switch's sending, under the head.** -/
theorem tieBySwitch_head (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat}
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l pw Qc blk)
    (h1 : 1 ≤ l) (hS : segmentsOf Zp Gr = segsW) {p : SwitchPlace} (hP : p ∈ switchPlaces Zp Gr)
    (hpw : placesW.find? (·.link == l) = some p) (lay : OnBytes.Params.ReqLayout) {N : Nat} (hN : N ≤ fxAt cF p)
    (msg : ∀ n, n + 1 < (switchSent p.sizes p.others).size →
      OwnMsgs Sc (𝕋).valid N (P5J.At.arr Zp (seatSw Zp p n).1 (seatSw Zp p n).2) (fxAt cF p)
        (switchMsgOff 0 rows readers (lotClosingAt lay (segmentsOf Zp Gr)) p n))
    (pad : ∀ n, n + 1 < (switchSent p.sizes p.others).size →
      OwnPads Sc (𝕋).valid (seatSw Zp p n).1 (seatSw Zp p n).2 (fun k _ => switchPadTxt 0 p n k))
    (book : ∀ n, n + 1 < (switchSent p.sizes p.others).size → ∃ e, (K12.Light.carriedOf Bk ⟨blk.place, 0⟩)[
        0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum + (0 + n)]? = some e ∧
      e.owner = ⟨p.place, 0⟩ ∧
      e.start = dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) n ∧
      e.count = messageDue p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape
        (K2.foldAt (switchFresh p.sizes p.others p.foldVars) n))
    (bookFront : ∀ n, n < 0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum →
      ∃ e e', (K12.Light.carriedOf Bk ⟨blk.place, 0⟩)[n]? = some e ∧
        (K12.Light.carriedOf Bk ⟨p.place, 0⟩)[n]? = some e' ∧
        e.owner = e'.owner ∧ e.start = e'.start ∧ e.count = e'.count)
    (hH : ∀ k : Coins Bk, ∃ c, handed 0 p k = some c)
    (hV : ∀ c v hd, (𝕋).valid v →
      ∃ V, switchRowsLaid rows readers (lotClosingAt lay (segmentsOf Zp Gr)) p c v hd = .ok V)
    (hD1 : ∀ (ξ : ProofFile.Inst) (i m : Nat) (a : MsgAddr), p.addrs i m = some a → i < l → (rows ξ).heardAt a ≤ fxAt cF p)
    (hzero : ∀ (ξ : ProofFile.Inst) (m : Nat), 1 + p.sizes.kept.length + m + 1 < (switchSent p.sizes p.others).size →
      (rows ξ).heardAt (p.ownAddr m) = 0) :
    TieBySwitch 𝕋 Sc Zp readers rows Gr Said l Qc blk (𝕋).valid lay (segmentsOf Zp Gr) p N (fxAt cF p) (seatSw Zp p) := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hl : l < 25 := link_lt h (List.getElem?_eq_some_iff.1 hblk).1
  have hQ : Qc.link = l := (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1
  have hlink : p.link = l := by
    have hbq := List.find?_some hpw
    exact eq_of_beq hbq
  obtain ⟨p', S₀, hp', hS₀, e1, e2, -, e4, -⟩ := pub_at h1 hl
  obtain rfl : p = p' := Option.some.inj (hpw.symm.trans hp')
  have hfront := lot_front hS hQ hl
  refine
    { msg := msg, pad := pad, book := book, bookFront := bookFront, chain := rfl, noWord := e4
      last := fun S hSl => ?_, front := ?_, first := fun S hSm => ?_, gam := fun S hSm => ?_
      stand := fun {k s m En ds y cols s'} St {D} Hb => ?_ }
  · rw [lot_last hS hQ hl, hS₀] at hSl
    obtain rfl : S₀ = S := Option.some.inj hSl
    exact ⟨e1, e2⟩
  · rw [hfront, hS, hlink]
  · rw [hfront] at hSm
    exact of_decide_eq_true (List.all_eq_true.1 first_written S (List.mem_of_mem_take hSm))
  · rw [hfront] at hSm
    exact fx_gam h h1 hl hpw S hSm
  · obtain ⟨hr, hf, -, -⟩ := stand_reached h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td St
    have hfx : fxAt cF p ≤ m.st.heard.length := fx_heard h h1 hl hpw rfl rfl St
    have hv := step_valid St
    obtain ⟨c, hc⟩ := hH k
    obtain ⟨V, hVc⟩ := hV c m.st.input (m.st.heard.take (fxAt cF p)) hv
    refine ⟨hv, Nat.le_trans hN hfx, hfx, ⟨c, hc, V, hVc⟩, switch_codes_at h h1 hl hpw hr hf,
      switch_seats_at h h1 hl hpw hr hf Hb.there, fun i S hi => ?_,
      own_now_at readers rows hS hQ h1 hl hP hpw m.st.input m.st.heard (hzero _)⟩
    refine own_front_at readers rows Qc hP m.st.input m.st.heard hfx hi fun m' a ha => hD1 _ (0 + i) m' a ha ?_
    have h3 := (List.getElem?_eq_some_iff.1 hi).1
    rw [hfront, List.length_take] at h3
    omega

/-- **The record on the fresh mask, under the head.** -/
theorem freshBySwitch_head (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat}
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l pw Qc blk)
    (h1 : 1 ≤ l) {p : SwitchPlace} (hpw : placesW.find? (·.link == l) = some p) (lay : OnBytes.Params.ReqLayout) {N : Nat}
    (hN : N ≤ fxAt cF p) (hvars : p.foldVars = Qc.k)
    (msg : OwnMsgs Sc (𝕋).valid N
      (P5J.At.arr Zp (seatSw Zp p ((switchSent p.sizes p.others).size - 1)).1
        (seatSw Zp p ((switchSent p.sizes p.others).size - 1)).2) (fxAt cF p)
      (switchMsgOff 0 rows readers (lotClosingAt lay (segmentsOf Zp Gr)) p ((switchSent p.sizes p.others).size - 1)))
    (pad : OwnPads Sc (𝕋).valid (seatSw Zp p ((switchSent p.sizes p.others).size - 1)).1
      (seatSw Zp p ((switchSent p.sizes p.others).size - 1)).2
      (fun k _ => switchPadTxt 0 p ((switchSent p.sizes p.others).size - 1) k))
    (book : ∀ e ∈ Bk.ahead, (e.spender == ⟨blk.place, 0⟩) = true → e.once = true → e.owner = ⟨p.place, 0⟩ ∧
      e.start.e = (dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)
          ((switchSent p.sizes p.others).size - 1)).e +
        fromE p.sizes.codes
          ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape)
    (hH : ∀ k : Coins Bk, ∃ c, handed 0 p k = some c)
    (hV : ∀ c v hd, (𝕋).valid v →
      ∃ V, switchRowsLaid rows readers (lotClosingAt lay (segmentsOf Zp Gr)) p c v hd = .ok V) :
    FreshBySwitch 𝕋 Sc Zp readers rows Said l Qc blk (𝕋).valid (lotClosingAt lay (segmentsOf Zp Gr)) p N (fxAt cF p)
      (seatSw Zp p ((switchSent p.sizes p.others).size - 1)).1
      (seatSw Zp p ((switchSent p.sizes p.others).size - 1)).2 := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hl : l < 25 := link_lt h (List.getElem?_eq_some_iff.1 hblk).1
  obtain ⟨p', S₀, hp', -, -, -, -, e4, e5⟩ := pub_at h1 hl
  obtain rfl : p = p' := Option.some.inj (hpw.symm.trans hp')
  refine
    { msg := msg, pad := pad, book := book, chain := rfl, noWord := e4, some := e5, vars := hvars
      stand := fun {k s m En ds y cols s'} St {D} Hb => ?_ }
  obtain ⟨hr, hf, -, -⟩ := stand_reached h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td St
  have hfx : fxAt cF p ≤ m.st.heard.length := fx_heard h h1 hl hpw rfl rfl St
  have hv := step_valid St
  obtain ⟨c, hc⟩ := hH k
  obtain ⟨V, hVc⟩ := hV c m.st.input (m.st.heard.take (fxAt cF p)) hv
  obtain ⟨q1, q2⟩ := mask_seat_at h h1 hl hpw hr hf Hb.mask
  exact ⟨hv, Nat.le_trans hN hfx, hfx, ⟨c, hc, V, hVc⟩, switch_codes_at h h1 hl hpw hr hf, q1, q2⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.stand_reached
#print axioms ProofFile.Honest.K10.tieBySwitch_head
#print axioms ProofFile.Honest.K10.freshBySwitch_head
