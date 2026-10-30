-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/RecordSendsPaid.lean: the kind "the code switch" (K2): THE
RECORD OF PREMISES `K2SeatedL` (Honest/K2/SeatedL.lean) AT THE FIRST THREAD's LETTERS AT THE
LIBRARY's HEAD, AT A SWITCH OF THE PLAN, WITH TWENTY-THREE OF ITS THIRTY FIELDS PAID AND SEVEN
HANDED ON. IT DOES NOT SAY THAT THE RECORD IS MET. One law: a join: `k2SeatedL_block_paid`
(Honest/K2/Law/RecordBlockPaid.lean) called with sends and books paid by `sends_books_at_head`
(Honest/K2/Law/SendsAtThread.lean). No definition; nothing is evaluated here.

THE LETTERS AND THE END: RecordBlockPaid.lean's, to the sign.

  `k2SeatedL_sends_paid`   THE END

Limits. HANDED ON, IN THE RECORD's OWN TEXT (out of SeatedL.lean): member (a block
stands there: `k2_member_at_head`, Honest/K2/Law/RecordAtHead.lean; blk is a letter here) · half
(the prover's record) · closes · publicAt · asks (public; they have payers that are not called here)
· msgs · pads (THE TIE: premises on the letter Q). D, readers, lay stay free letters. h: the
library's head: A HYPOTHESIS. All limits of the two files named stand. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.RecordBlockPaid
import Johnson.Desc.ProofFile.Honest.K2.Law.SendsAtThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (S Numbers Item rowSays wordsAtFirst)
open VerifiableInference.Desc.First.K2 (P2 decideWith)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed)
open VerifiableInference.Desc.K2.Honest (carryExact)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (seatAtMember)
open Johnson.Prover.Send (shapeAt)
open _root_.Desc.Plain (DState)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {blk : Block TS ProofFile.Cl} {D : RowDataOf ProofFile.Inst}
  {readers : Local W₀ Rc ProofFile.Inst Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {p : SwitchPlace}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **AT lettersHead, AT A SWITCH OF THE PLAN: TWENTY-THREE FIELDS PAID, SEVEN HANDED ON** in the
record's own text. n, nm, st, before and after stand under "there are", with what ties them. -/
theorem k2SeatedL_sends_paid
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (hX : carryX = carryExact Zp (P5J.At.arr Zp))
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    (member : L.bs[(P5J.At.ps.findIdx (· == p.place))]? = some blk)
    (half : (L.hs.find? fun g => g.place == p.place) = some (switchHalf (coreSender freshTable) D
      readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p))
    (closes : closingOk freshTable ((segmentsOf Zp Bs.G₀).take p.link) p = true)
    (publicAt : ∀ w, L.valid w → publicOk D lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true)
    (msgs : ∀ n, n < (switchPar p).sent.size → OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs
      (P5J.At.ps.findIdx (· == p.place))) ((P5J.At.arr Zp) (seatAtMember L.bs (P5J.At.ps.findIdx (·
      == p.place)) (switchPar p) n).1 (seatAtMember L.bs (P5J.At.ps.findIdx (· == p.place))
      (switchPar p) n).2) (L.thread.front + roundsTo L.bs (P5J.At.ps.findIdx (· == p.place)))
      (switchMsgOff 0 D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n))
    (pads : ∀ n, n < (switchPar p).sent.size → OwnPads L.Q L.valid (seatAtMember L.bs
      (P5J.At.ps.findIdx (· == p.place)) (switchPar p) n).1 (seatAtMember L.bs (P5J.At.ps.findIdx
      (· == p.place)) (switchPar p) n).2 (fun k _ => switchPadTxt 0 p n k))
    (asks : Item.carry (p.link - 1) ∈ L.thread.opened (P5J.At.ps.findIdx (· == p.place))) :
    ∃ (Pp : P1K2.Prep) (n : P1K2.Nums) (nm : String) (st : VerifiableInference.Desc.First.K2.At)
      (before : TS → Except String TS) (after : TS → TS → Except String TS),
      P1K2.prepOf Zp Bs.G₀ = some Pp ∧ P1K2.numsAt Pp p.place.link = some n ∧
      SwitchArm Zp Bs.G₀ p st before after ∧
      K2SeatedL L (P5J.At.ps.findIdx (· == p.place)) blk D readers lay (segmentsOf Zp Bs.G₀) p
        (IM.k2P Zp p.place nm st n) before after p.link (L.N.msgsAt (some p.place)) Zp
        (P5J.At.arr Zp) (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay)
        (K1.radRec (3 * p.link) (switchPar p)) :=
  k2SeatedL_block_paid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL hX O hp member half
    (sends_books_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL O hp member).1
    (sends_books_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL O hp member).2
    closes publicAt msgs pads asks

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.k2SeatedL_sends_paid
