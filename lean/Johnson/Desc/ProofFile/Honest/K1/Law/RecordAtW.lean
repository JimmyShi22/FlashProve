-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RecordAtW.lean: THE RECORD OF PREMISES K1Seated
(Honest/K1/Seated.lean) AT W's SENDING (number 356 of the first chain's flat list), AT ProofFile's LETTERS
AT THE LIBRARY's HEAD (lettersHead, Honest/Thread/FirstHead.lean): WHAT IS LEFT WHEN ALL THAT LIES
IS SPENT. One theorem; no definition. IT DOES NOT SAY THAT THE RECORD IS MET: five fields stay
premises.

  - k1Seated_w_paid: UNDER h (the library's head: A HYPOTHESIS) and the two equations hL · hJ, which
    a caller meets by rfl: at the job wJobAt Zp.first (wGp Zp) 4 wMsgFull (lotNo secondHashFunction Zp ‹W's
    place›) Dw (Honest/K1/PlaceW.lean), AT EVERY FILLING Dw OF THE DATA, at the sort .w and the
    radii K1.radRec 81 J.P: K1Seated L 356 …. FIFTEEN PAID. HANDED ON, FIVE, in the record's own
    text: member · half · hasCoins · msgs · pads.

Who pays. placeAt: place356W (SeatsAtW.lean) · shape, isSend, books: k1_w_inScope (MemberAtW.lean),
at the message that msg_w_head names (FitsAtW.lean) · fits, oneAns, port: FitsAtW.lean · heardOnly:
by placeJob's text · firstNo: firstNo_laid (FirstNoTold.lean) · seats, numbered, sits:
SeatsAtW.lean; numbered's number by firstNo · treesNo, ans, rowM: k1Seated_at_head
(RecordAtHead.lean), which this theorem calls.

ALOUD. half CAN BE MET ONLY AT A PROVER WHOSE LIST OF HALVES HAS wSide's HALF
(Honest/K1/PlaceW.lean) AT W's PLACE: at widerFillAt none stands there (wider_none_at_w,
WSideAtFill.lean): AT A PROVER WITHOUT IT THE THEOREM HOLDS OF NOTHING. Dw IS A FREE LETTER:
nothing is said of what the data are. H, Q, wit, own₀, Bk and w are free letters, as in
RecordAtHead.lean: hasCoins can be paid only at a named book; THE TIE (msgs, pads) IS A PREMISE
ON THE LETTER Q, asked at one input w.

Limits. THE FULL SIZE ALONE. That the head holds is a hypothesis. IT STANDS OVER FILES OF ProofFile's THAT
ARE ON NO SEAL. It counts in no column. Nothing on soundness, on completeness or on any other
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.MemberAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.FirstNoTold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open Johnson.Prover.Send (shapeAt)

/-- **NUMBER 356, AT lettersHead, AT EVERY FILLING OF THE DATA: FIFTEEN PAID**; member, half,
hasCoins, msgs and pads are handed on. -/
theorem k1Seated_w_paid {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} (Dw : RowDataOf ProofFile.Inst)
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull
      (lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩) Dw)
    {own₀ : X} {blk : Block TS ProofFile.Cl}
    (member : L.bs[356]? = some blk)
    (half : (L.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (hasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride)
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs 356)
        ((P5J.At.arr Zp) (seatAtMember L.bs 356 J.P n).1 (seatAtMember L.bs 356 J.P n).2)
        (L.thread.front + roundsTo L.bs 356) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs 356 J.P n).1 (seatAtMember L.bs 356 J.P n).2
        (fun k _ => padTxt 0 J n k)) :
    K1Seated L 356 blk wit J own₀ .w (P5J.At.arr Zp) (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay)
      (K1.radRec 81 J.P) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hm : cF.blocksInOrder[356]? = some blk := by rw [hL] at member; exact member
  obtain ⟨msg, hmsg, h1, h2, h3⟩ := k1_w_inScope h.scope h.reads O hm
  obtain rfl : msg = wMsgFull := Option.some.inj (hmsg.symm.trans (msg_w_head h O))
  have hp : P5J.At.ps[356]? = some ⟨1, none, 4, .K1⟩ := place356W
  have hN : (P5J.At.N Zp cF).msgsAt (some ⟨1, none, 4, .K1⟩) =
      lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩ :=
    firstNo_laid h.scope h.reads h.laid (List.mem_of_getElem? hp)
  subst hJ
  refine k1Seated_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL rfl member
    (by rw [hL]; exact hp) h1 half h2 h3 (fits_w_head h O)
    (fun v fr fr' e => by simp only [wJobAt, placeJob, e]) (oneAns_w_head h O) hasCoins
    (by rw [hL]; exact hN) (port_w_head h O) msgs pads ?_ ?_ ?_
  · subst hL
    exact seats_w h O
  · subst hL
    have e := numbered_w h O
    rw [show (K1.parW Zp.first (wGp Zp) 4 wMsgFull).place = ⟨1, none, 4, .K1⟩ from rfl, hN] at e
    exact e
  · subst hL
    exact sits_w h O

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1Seated_w_paid
