-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ShrHead.lean: the closing of a segment (K10): THE TWO RECORDS OF THE SHARED SENDING (the kind K1): `TieByShared`
(Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieByShared.lean) and `FreshByShared` (Pay/XchFreshField.lean), UNDER THE HEAD, at the first chain's
thread: every public field and every clause at a stand that this file's authors pay is paid; what is left stands as named premises. And the
count of the first segment's group that `threeLeft_at_first` (Pay/XchThreeLeft.lean) asks.

The sender's job J is a variable with one equation on its plan (hJ): J.P is the library's plan of the opening, or of a later moment, at any
first-chain parameters q with the written shape and codes (hs, hc) and any gp. Its data and its riding tables stay free.

  `shrCodes_written`, `shrCodes_bent`   a closed test, by Lean's kernel, with a control that fails: each written segment has the written codes
  **`tieByShared_later_head`**   each segment, both later moments (d): the record at: the thread's own valid inputs; N and front the number of
      rounds in front of the sending; the one message; the seat `seatAtMember`
  **`tieByShared_open_head`**    the first segment: the opening's messages 0, 1, 2
  **`freshByShared_head`**       the first segment: the opening's message 3, the fold's fresh mask
  **`shr_hcount_head`**          the first segment: the group has at most 3 + 1 + 1 members

PAID: chain · codes · of stand: the input is valid; enough challenges have been heard (twice); the statement's codes are the sender's; each of
these members has its seat and the sender's shape; the fresh mask's message has its shape and its seat.
LEFT AS PREMISES:
      on the script   msg, pad
      on the book     book · hcut: the sender's part has its cut at every run's coins
      public          ride, padOk, word (tie) · room (fresh) · hS: the segments are the written ones
      at a stand      hdata (tie): the closing's job's shape and data for the member are the sender's · hride (fresh): the table that rides at
                      message 3 is the fold's

By: AtFullSide/K10/ShrSeatsAt.lean; `stand_reached` (Pay/XchSwitchHead.lean); `step_valid`, `step_heard_le` (Pay/XchStand.lean); `facts_reached`
(Pay/AtReach.lean); `lot_last` (Pay/XchPublic.lean); `AtMg.codes_full`.

Limits. The head is a premise. That a run stands at the border is not shown. The full size and the older hash alone. This file proves no
property of a prover or a protocol.
-/
import AtFullSide.K10.ShrSeatsAt
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSwitchHead
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieByShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open VerifiableInference.Desc (Block Chain Place Strs OpenedColumn)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K1 (noL firstPar parLater)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.Sound (MsgT seatBy noFirst)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (codesFull2)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest ProofFile.Honest.FirstThread ProofFile.Honest.K10
open ProofFile.Honest.K1 (seatAtMember SendJob)
open ProofFile.Honest.K2 (segmentsOf asRow)
open ProofFile.Honest.K2.Law (segsW)
open ProofFile.Honest.K10.LeftIs (stageB)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

set_option maxRecDepth 1000000 in
/-- Each written segment has the written codes. -/
theorem shrCodes_written : (segsW.all fun S => decide (S.sizes.codes = codesFull2)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: at the written codes without their mask codes it rejects every segment. -/
theorem shrCodes_bent : (segsW.any fun S => decide (S.sizes.codes = { codesFull2 with mask := #[] })) = false := by
  decide +kernel

/-- A later moment's sending stands in front of the segment's closing. -/
theorem shr_noL_le (l : Nat) (d : Bool) : noL l d ≤ 14 * l + IM.nAt l + 5 := by
  have h7 : 7 ≤ IM.nAt l := by
    unfold IM.nAt
    split <;> omega
  have h6 : IM.k1Ix l d ≤ 6 := by
    unfold IM.k1Ix
    split <;> split <;> omega
  show 14 * l + IM.k1Ix l d + 2 ≤ _
  omega

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

/-- The last segment's codes are the written ones. -/
theorem shr_last_codes {Gr : ProofFile.Ground} {Qc : Par} {l : Nat} (hS : segmentsOf Zp Gr = segsW) (hQ : Qc.link = l) (hl : l < 25) :
    ∀ S, (lotSegs Zp Gr Qc).getLast? = some S → S.sizes.codes = codesFull2 := by
  intro S hSl
  rw [lot_last hS hQ hl] at hSl
  exact of_decide_eq_true (List.all_eq_true.1 shrCodes_written S (List.mem_of_getElem? hSl))

/-- **The record on a later moment's sending, under the head.** -/
theorem tieByShared_later_head {Wj Xj : Type} (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst)
    (Gr : ProofFile.Ground) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat}
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l pw Qc blk)
    (hS : segmentsOf Zp Gr = segsW) {q : OnBytes.Params.First} (hs : q.shape = shapeFull) (hc : q.codes = codesFull2)
    (gp : _root_.Desc.Plain.GPar) (d : Bool) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (J : SendJob Wj Xj)
    (hJ : J.P = parLater q gp l (IM.k1Ix l d + 1) (if d then 2 else 1)) (own₀ : Xj) {c lo : Nat}
    (hpos : shrPosLater l = some c) (hlo : lo = c + (if d then 1 else 0))
    (msg : ∀ n, n < 1 → OwnMsgs Sc (𝕋).valid (0 + roundsTo cF.blocksInOrder (noL l d))
      (P5J.At.arr Zp (seatAtMember cF.blocksInOrder (noL l d) J.P n).1 (seatAtMember cF.blocksInOrder (noL l d) J.P n).2)
      (0 + roundsTo cF.blocksInOrder (noL l d)) (ProofFile.Honest.K1.msgTxt 0 wit J own₀ n))
    (pad : ∀ n, n < 1 → OwnPads Sc (𝕋).valid (seatAtMember cF.blocksInOrder (noL l d) J.P n).1
      (seatAtMember cF.blocksInOrder (noL l d) J.P n).2 (fun k _ => ProofFile.Honest.K1.padTxt 0 J n k))
    (book : ∀ n, n < 1 → ∃ e, (K12.Light.carriedOf Bk ⟨blk.place, 0⟩)[
        0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum + (lo + n)]? = some e ∧
      e.owner = ⟨J.P.place, 0⟩ ∧ e.start = ProofFile.Honest.K1.startR J.P J.ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR J.P J.ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR J.P J.ride).e)
    (ride : ∀ n, n < 1 → J.ride n = none)
    (padOk : ∀ n, n < 1 → (ProofFile.Honest.K1.stepsOf J.P.codes (shapeAt J.P n) none).pad ≤
      (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (word : ∀ n, n < 1 → (shapeAt J.P n).mainRows = 0 ∨ (shapeAt J.P n).answers ≠ 0)
    (hcut : ∀ k : Coins Bk, ∃ c, ProofFile.Honest.K1.lentCut k 0 ⟨J.P.place, 0⟩ (ProofFile.Honest.K1.dueR J.P J.ride) = some c)
    (hdata : ∀ {k s m En ds y cols s'}, StepAt 𝕋 Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ n, n < 1 → ∀ (ca : CsAll (closeCarries ⟨Qc, borneAt Zp Qc⟩)) (a : ProofFile.Honest.K2.Law.Laid) (nn : Nat),
        LotMember readers rows Zp Gr Qc m.st.input m.st.heard ca (lo + n) a nn →
        a.1 = shapeAt J.P n ∧ a.2 = fun r i => asRow ((shapeAt J.P n).mainDeg == 3)
          (J.data (wit m.st.input)
            { heard := m.st.heard.take (0 + roundsTo cF.blocksInOrder (noL l d)), own := own₀, seen := .bare [] } n r i)) :
    TieByShared 𝕋 Sc Zp readers rows Gr Said l Qc blk (𝕋).valid wit J own₀ (0 + roundsTo cF.blocksInOrder (noL l d))
      (0 + roundsTo cF.blocksInOrder (noL l d)) lo 1 (seatAtMember cF.blocksInOrder (noL l d) J.P) := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hl : l < 25 := link_lt h (List.getElem?_eq_some_iff.1 hblk).1
  have hQ : Qc.link = l := (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1
  have hJc : J.P.codes = codesFull2 := by
    rw [hJ]
    exact hc
  refine
    { msg := msg, pad := pad, book := book, chain := rfl, ride := ride, padOk := padOk, word := word
      codes := fun S hSl => (shr_last_codes hS hQ hl S hSl).trans hJc.symm
      stand := fun {k s m En ds y cols s'} St {D} Hb => ?_ }
  obtain ⟨hr, hf, -, -⟩ := stand_reached h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td St
  have hle : 0 + roundsTo cF.blocksInOrder (noL l d) ≤ m.st.heard.length := step_heard_le rfl St (shr_noL_le l d)
  refine ⟨step_valid St, hle, hle, hcut k, ?_, ?_, hdata St⟩
  · rw [(facts_reached h hr hf).2.1, P5J.AtMg.codes_full h.toAtMg, hJc]
  · rw [hJ]
    exact shr_later_seats h hl hs hc gp hr hf Hb.there d hpos hlo

/-- **The record on the opening's first three messages, under the head, at the first segment.** -/
theorem tieByShared_open_head {Wj Xj : Type} (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst)
    (Gr : ProofFile.Ground) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp 0 pw Qc blk)
    (hS : segmentsOf Zp Gr = segsW) {q : OnBytes.Params.First} (hs : q.shape = shapeFull) (hc : q.codes = codesFull2)
    (gp : _root_.Desc.Plain.GPar) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (J : SendJob Wj Xj) (hJ : J.P = firstPar q gp)
    (own₀ : Xj)
    (msg : ∀ n, n < 3 → OwnMsgs Sc (𝕋).valid (0 + roundsTo cF.blocksInOrder 2)
      (P5J.At.arr Zp (seatAtMember cF.blocksInOrder 2 J.P n).1 (seatAtMember cF.blocksInOrder 2 J.P n).2)
      (0 + roundsTo cF.blocksInOrder 2) (ProofFile.Honest.K1.msgTxt 0 wit J own₀ n))
    (pad : ∀ n, n < 3 → OwnPads Sc (𝕋).valid (seatAtMember cF.blocksInOrder 2 J.P n).1
      (seatAtMember cF.blocksInOrder 2 J.P n).2 (fun k _ => ProofFile.Honest.K1.padTxt 0 J n k))
    (book : ∀ n, n < 3 → ∃ e, (K12.Light.carriedOf Bk ⟨blk.place, 0⟩)[
        0 + ((lotSegs Zp Gr Qc).dropLast.map (·.messages)).sum + (0 + n)]? = some e ∧
      e.owner = ⟨J.P.place, 0⟩ ∧ e.start = ProofFile.Honest.K1.startR J.P J.ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR J.P J.ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR J.P J.ride).e)
    (ride : ∀ n, n < 3 → J.ride n = none)
    (padOk : ∀ n, n < 3 → (ProofFile.Honest.K1.stepsOf J.P.codes (shapeAt J.P n) none).pad ≤
      (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (word : ∀ n, n < 3 → (shapeAt J.P n).mainRows = 0 ∨ (shapeAt J.P n).answers ≠ 0)
    (hcut : ∀ k : Coins Bk, ∃ c, ProofFile.Honest.K1.lentCut k 0 ⟨J.P.place, 0⟩ (ProofFile.Honest.K1.dueR J.P J.ride) = some c)
    (hdata : ∀ {k s m En ds y cols s'}, StepAt 𝕋 Said (14 * 0 + IM.nAt 0 + 5) blk k s m En ds y cols s' →
      ∀ n, n < 3 → ∀ (ca : CsAll (closeCarries ⟨Qc, borneAt Zp Qc⟩)) (a : ProofFile.Honest.K2.Law.Laid) (nn : Nat),
        LotMember readers rows Zp Gr Qc m.st.input m.st.heard ca (0 + n) a nn →
        a.1 = shapeAt J.P n ∧ a.2 = fun r i => asRow ((shapeAt J.P n).mainDeg == 3)
          (J.data (wit m.st.input)
            { heard := m.st.heard.take (0 + roundsTo cF.blocksInOrder 2), own := own₀, seen := .bare [] } n r i)) :
    TieByShared 𝕋 Sc Zp readers rows Gr Said 0 Qc blk (𝕋).valid wit J own₀ (0 + roundsTo cF.blocksInOrder 2)
      (0 + roundsTo cF.blocksInOrder 2) 0 3 (seatAtMember cF.blocksInOrder 2 J.P) := by
  have hQ : Qc.link = 0 := (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1
  have hJc : J.P.codes = codesFull2 := by
    rw [hJ]
    exact hc
  refine
    { msg := msg, pad := pad, book := book, chain := rfl, ride := ride, padOk := padOk, word := word
      codes := fun S hSl => (shr_last_codes hS hQ (by omega) S hSl).trans hJc.symm
      stand := fun {k s m En ds y cols s'} St {D} Hb => ?_ }
  obtain ⟨hr, hf, -, -⟩ := stand_reached h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td St
  have hle : 0 + roundsTo cF.blocksInOrder 2 ≤ m.st.heard.length := step_heard_le rfl St (by decide)
  refine ⟨step_valid St, hle, hle, hcut k, ?_, ?_, hdata St⟩
  · rw [(facts_reached h hr hf).2.1, P5J.AtMg.codes_full h.toAtMg, hJc]
  · rw [hJ]
    exact shr_open_seats h hs hc gp hr hf Hb.there

/-- **The record on the first segment's fresh mask, under the head.** -/
theorem freshByShared_head {Wj Xj : Type} (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp 0 pw Qc blk)
    {q : OnBytes.Params.First} (hs : q.shape = shapeFull) (hc : q.codes = codesFull2)
    (gp : _root_.Desc.Plain.GPar) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (J : SendJob Wj Xj) (hJ : J.P = firstPar q gp)
    (own₀ : Xj)
    (msg : OwnMsgs Sc (𝕋).valid (0 + roundsTo cF.blocksInOrder 2)
      (P5J.At.arr Zp (seatAtMember cF.blocksInOrder 2 J.P 3).1 (seatAtMember cF.blocksInOrder 2 J.P 3).2)
      (0 + roundsTo cF.blocksInOrder 2) (ProofFile.Honest.K1.msgTxt 0 wit J own₀ 3))
    (pad : OwnPads Sc (𝕋).valid (seatAtMember cF.blocksInOrder 2 J.P 3).1 (seatAtMember cF.blocksInOrder 2 J.P 3).2
      (fun k _ => ProofFile.Honest.K1.padTxt 0 J 3 k))
    (book : ∀ e ∈ Bk.ahead, (e.spender == ⟨blk.place, 0⟩) = true → e.once = true → e.owner = ⟨J.P.place, 0⟩ ∧
      e.start.e = ProofFile.Honest.K1.maskStart J.P J.ride 3)
    (room : ProofFile.Honest.K1.maskStart J.P J.ride 3 + (2 * Qc.k + 1) ≤ (ProofFile.Honest.K1.dueR J.P J.ride).e)
    (hcut : ∀ k : Coins Bk, ∃ c, ProofFile.Honest.K1.lentCut k 0 ⟨J.P.place, 0⟩ (ProofFile.Honest.K1.dueR J.P J.ride) = some c)
    (hride : ∀ {k s m En ds y cols s'}, StepAt 𝕋 Said (14 * 0 + IM.nAt 0 + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (VerifiableInference.Desc.K9.recOf s) D →
        J.ride 3 = some ⟨Qc.k, (stageB D (VerifiableInference.Desc.K9.recOf s)).h⟩) :
    FreshByShared 𝕋 Sc Zp Said 0 Qc blk (𝕋).valid wit J own₀ (0 + roundsTo cF.blocksInOrder 2) (0 + roundsTo cF.blocksInOrder 2) 3
      (seatAtMember cF.blocksInOrder 2 J.P 3).1 (seatAtMember cF.blocksInOrder 2 J.P 3).2 := by
  have hJc : J.P.codes = codesFull2 := by
    rw [hJ]
    exact hc
  refine
    { msg := msg, pad := pad, book := book, chain := rfl, room := room
      stand := fun {k s m En ds y cols s'} St {D} Hb => ?_ }
  obtain ⟨hr, hf, -, -⟩ := stand_reached h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td St
  have hle : 0 + roundsTo cF.blocksInOrder 2 ≤ m.st.heard.length := step_heard_le rfl St (by decide)
  obtain ⟨q1, q2⟩ := shr_mask_seat h hs hc gp hr hf Hb.mask
  refine ⟨step_valid St, hle, hcut k, hride St Hb, ?_, ?_, ?_⟩
  · rw [(facts_reached h hr hf).2.1, P5J.AtMg.codes_full h.toAtMg, hJc]
  · rw [hJ]
    exact q1
  · rw [hJ]
    exact q2

/-- **The count of the first segment's group, at a stand.** -/
theorem shr_hcount_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp 0 pw Qc blk) :
    ∀ {k s m En ds y cols s'}, StepAt 𝕋 Said (14 * 0 + IM.nAt 0 + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (VerifiableInference.Desc.K9.recOf s) D → D.G.members.size ≤ 3 + 1 + 1 := by
  intro k s m En ds y cols s' St D Hb
  obtain ⟨hr, hf, -, -⟩ := stand_reached h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td St
  exact shr_count_zero h hr hf Hb.there

end AtFullSide.K10

#print axioms AtFullSide.K10.shrCodes_written
#print axioms AtFullSide.K10.shrCodes_bent
#print axioms AtFullSide.K10.shr_noL_le
#print axioms AtFullSide.K10.shr_last_codes
#print axioms AtFullSide.K10.tieByShared_later_head
#print axioms AtFullSide.K10.tieByShared_open_head
#print axioms AtFullSide.K10.freshByShared_head
#print axioms AtFullSide.K10.shr_hcount_head
