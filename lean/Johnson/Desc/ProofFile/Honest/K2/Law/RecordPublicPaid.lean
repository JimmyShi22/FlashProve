-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/RecordPublicPaid.lean: the kind "the code switch" (K2): THE
RECORD OF PREMISES `K2SeatedL` (Honest/K2/SeatedL.lean) AT THE FIRST THREAD's LETTERS AT THE
LIBRARY's HEAD, AT A SWITCH OF THE PLAN, WITH NINETEEN OF ITS THIRTY FIELDS PAID AND ELEVEN HANDED
ON. IT DOES NOT SAY THAT THE RECORD IS MET. One law: a join: `k2SeatedL_at_place`
(Honest/K2/Law/RecordAtHead.lean) called with eight fields more and its premise hcodes paid. No
definition; nothing is evaluated here.

THE LETTERS: b := the number where the written list of places first bears the place · seg := the
place's link · segs := the plan's own segments · first := the table's own count of messages in front
of the place · arr, seats₀, ms := the real table's · q := `IM.k2P` Zp a nm st n, n: the plan's own
numbers at the place's link; a, nm, st: FREE: the field shape, which is handed on, pins them · rad
:= the radii of entry 3 l of the written record, l: the place's link · carryX := the exact carry
(hX).

  `k2SeatedL_public_paid`   PAID BESIDE THE ELEVEN OF `k2SeatedL_at_place`: hcodes
                    (`codes_switch`) · trees · answersNo · seedsNo · nonZeroNo
                    (`four_public_at_head`) · port (`port_switch`), all
                    Honest/K2/Law/PublicMoreAtHead.lean · seats · numbered · sits (`seats_switch`,
                    `numbered_switch`, `sits_switch`, Honest/K2/Law/SeatsAtSwitches.lean)

Limits. HANDED ON, IN THE RECORD's OWN TEXT (SeatedL.lean): member · shape ·
decides · sends · books (the member's block) · half (the prover's record) · closes · publicAt
(public; they have payers that are not called here) · msgs · pads (THE TIE: premises on the letter
Q) · asks. D, readers, lay, before, after stay free letters. h: the library's head: A HYPOTHESIS.
All limits of the three files named stand. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SeatsAtSwitches
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicMoreAtHead

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
  {p : SwitchPlace} {before : TS → Except String TS}
  {after : TS → TS → Except String TS}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **AT lettersHead, AT A SWITCH OF THE PLAN: NINETEEN FIELDS PAID, ELEVEN HANDED ON** in the
record's own text. n: the plan's own numbers at the place's link (hP, hn); a, nm, st: free. -/
theorem k2SeatedL_public_paid
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (hX : carryX = carryExact Zp (P5J.At.arr Zp))
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) (a : Place) (nm : String)
    (st : VerifiableInference.Desc.First.K2.At)
    (member : L.bs[(P5J.At.ps.findIdx (· == p.place))]? = some blk)
    (shape : blk.place = p.place ∧ blk.rounds = First.K2.rounds (IM.k2P Zp a nm st n) ∧ blk.oracles
      = [(IM.k2P Zp a nm st n).sent, []])
    (half : (L.hs.find? fun g => g.place == p.place) = some (switchHalf (coreSender freshTable) D
      readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p))
    (decides : ∀ s rs gs t, rs.length = 2 → gs.length = (IM.k2P Zp a nm st n).read.length →
      (blk.decide s rs gs = .ok t ↔ ∃ s₁ m, before s = .ok s₁ ∧ decideWith _root_.Tw.K2.sendByL8
      (IM.k2P Zp a nm st n) s₁ rs gs = .ok m ∧ after s₁ m = .ok t))
    (sends : ∀ k s m E s' r₁ r₂ gs, Thr L.thread (P5J.At.ps.findIdx (· == p.place)) k s m E →
      blk.decide s [r₁, r₂] gs = .ok s' → ∃ (Lt : Type) (d d' : DState Lt) (owed : Option Nat) (ids
      : Array Nat), K1.decideSend (switchPar p) owed d [r₁, K1.cutTo (switchPar p) r₂] = .ok (ids,
      d') ∧ K1.SameMsgs d'.st s'.st ∧ s'.st.oracles.size = d'.st.oracles.size)
    (books : ∀ k s m E s' r₁ r₂ gs, Thr L.thread (P5J.At.ps.findIdx (· == p.place)) k s m E →
      blk.decide s [r₁, r₂] gs = .ok s' → K1.Booked (switchPar p) s.book s.st.oracles.size s'.book
      s'.st.oracles.size)
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
    K2SeatedL L (P5J.At.ps.findIdx (· == p.place)) blk D readers lay (segmentsOf Zp Bs.G₀) p
      (IM.k2P Zp a nm st n) before after p.link (L.N.msgsAt (some p.place)) Zp (P5J.At.arr Zp)
      (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay) (K1.radRec (3 * p.link) (switchPar p)) := by
  have F := four_public_at_head h O hp hP hn a nm st
  exact k2SeatedL_at_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL hX O hp
    (codes_switch h O hp)
    member shape half decides sends books closes publicAt F.1 F.2.1 F.2.2.1 F.2.2.2
    (port_switch h O hp) msgs pads (by subst hL; exact seats_switch h O hp)
    (by subst hL; exact numbered_switch h O hp) (by subst hL; exact sits_switch h O hp) asks

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.k2SeatedL_public_paid
