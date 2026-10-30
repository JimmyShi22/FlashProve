-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RecordPaidAtFill.lean: THE SHARED "SENDING" (the kind K1): THE
RECORD OF PREMISES K1Seated AT THE 51 REAL MEMBERS, AT A FILLING THAT IS A LETTER: SIXTEEN OF ITS
TWENTY FIELDS PAID. Two theorems; no definition.

  - k1Seated_two_fill_paid, k1Seated_fifty_fill_paid: UNDER h, hA (onlineProverFromPublicFiles returns A at the filling
    P), hex, ho (RecordAtFill.lean), eno : no = lotNo secondHashFunction A.Z: member, hasCoins, msgs and pads
    are handed on; the other sixteen fields are paid.

How made. THE TEXT OF THE TWO LAWS OF A FILE THAT IS HANDED IN TO NO LIST
(RecordPaid.lean: nailed to one filling), TURNED BY PROGRAM as RecordAtFill.lean's head tells; each
proof begins with "subst eno". The elder file does not turn. THIS FILE DOES NOT IMPORT IT.

`K1Seated` is had here only under the head, a returned prover, two premises on the lots and THE
TIE; here THE TIE is shown at no Script that a run has. At the first Script, under the head and a
returned prover alone: `k1Seated_first` (AtFullSide/K1/FirstScript.lean). HERE FOUR OF THE TWENTY
FIELDS ARE HANDED ON: member, hasCoins, msgs and pads; msgs and pads are THE TIE.
NOT IN FRONT OF A LAW OVER COINS.

Limits. As RecordAtFill.lean's. Nothing on any property.
AN IDLE WAY. L.valid is "v = w and Vd v": at Vd := fun _ => False it holds of nothing: msgs and
pads, which speak at the thread's valid inputs, are then met for nothing, and the record that
follows binds nothing at any input.
msgs AND pads ARE PROVED OF NO SCRIPT: no Script is shown that meets them at ProofFile's real letters.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtFill
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtTwo
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtFifty

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (S Numbers rowSays wordsAtFirst)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open Johnson.Prover.Send (shapeAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **NUMBER 2, AT THE EARLIER HASH: SIXTEEN PAID**; member, hasCoins, msgs and pads are handed on.
-/
theorem k1Seated_two_fill_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (eno : no = lotNo OnBytes.secondHashFunction A.Z) {Bk : ProverCoinCounts}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = placeJob (K1.firstPar A.G.first (K1.gpOf A.Z)) (no ⟨1, some 0,
        1, .K1⟩)
      (firstFold A.G.first) (Dt A.Z A.G))
    {blk : Block TS ProofFile.Cl}
    (member : L.bs[2]? = some blk)
    (hasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride)
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs 2)
        ((P5J.At.arr Zp) (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2)
        (L.thread.front + roundsTo L.bs 2) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2
        (fun k _ => padTxt 0 J n k)) :
    K1Seated L 2 blk wit J own₀ .opening (P5J.At.arr Zp) (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay)
      (K1.radRec 0 J.P) := by
  subst eno
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hT := treesNo_atN Zp cF ps_two
  have hN := firstNo_atPure h hA ps_two
  rw [eZ] at hN
  refine k1Seated_two_fill_no h hA wit _ Dt hex ho rfl Q test carryX item n₁ n₂ b₀ Vd Rd Kp w own₀
      hL hJ member ?_ ?_
      hasCoins msgs pads ?_ ?_ ?_
  · rw [hJ]
    show sendFits (K1.firstPar A.G.first (K1.gpOf A.Z)) (rideOf (firstFold A.G.first)) = true
    rw [eZ, eG]
    exact fits_two_head h O
  · rw [hJ]
    show answersAtMostOne (K1.firstPar A.G.first (K1.gpOf A.Z)) = true
    rw [eZ, eG]
    exact oneAns_two_head h O
  · subst hL hJ
    rw [eZ, eG]
    exact seats_two h O hT
  · subst hL hJ
    have e := numbered_two h O hT
    rw [show (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place = ⟨1, some 0, 1, .K1⟩ from rfl, hN] at e
    rw [eZ, eG]
    exact e
  · subst hL hJ
    rw [eZ, eG]
    exact sits_two h O hT

/-- **EACH OF THE FIFTY, AT THE EARLIER HASH: SIXTEEN PAID**; member, hasCoins, msgs and pads are
handed on. -/
theorem k1Seated_fifty_fill_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit no Dt A.Z A.G)
    (eno : no = lotNo OnBytes.secondHashFunction A.Z) {Bk : ProverCoinCounts}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {l : ℕ} (hl : l < 25) (d : Bool) {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = laterJobAt A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1)
      (no ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt A.Z A.G))
    {blk : Block TS ProofFile.Cl}
    (member : L.bs[(K1.noL l d)]? = some blk)
    (hasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride)
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs (K1.noL l d))
        ((P5J.At.arr Zp) (seatAtMember L.bs (K1.noL l d) J.P n).1 (seatAtMember L.bs (K1.noL l d)
            J.P n).2)
        (L.thread.front + roundsTo L.bs (K1.noL l d)) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs (K1.noL l d) J.P n).1 (seatAtMember L.bs (K1.noL l d)
          J.P n).2
        (fun k _ => padTxt 0 J n k)) :
    K1Seated L (K1.noL l d) blk wit J own₀ (cond d (.digits l) (.reads l))
      (P5J.At.arr Zp) (P5J.At.seats Zp)
      (P5J.At.ms Zp Z.lay) (K1.radRec (3 * l + (if d then 2 else 1)) J.P) := by
  subst eno
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  refine k1Seated_fifty_fill_no h hA wit _ Dt hex ho rfl Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      own₀ hL hl d hJ member
      ?_ ?_ hasCoins msgs pads ?_ ?_ ?_
  · rw [hJ]
    show sendFits (K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1))
      (rideOf none) = true
    rw [eZ, eG, ← parL_later]
    exact fits_fifty_head h O hl d
  · rw [hJ]
    show answersAtMostOne
      (K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1)) = true
    rw [eZ, eG, ← parL_later]
    exact oneAns_fifty_head h O hl d
  · subst hL hJ
    show ∀ y, y ∈ pinsAtSort (P5J.At.N Zp cF) (cond d (.digits l) (.reads l)) ↔ ∃ n,
      n < (K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1)).sent.size ∧
      (shapeAt (K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1))
        n).answers ≠ 0 ∧ y = seatAtMember cF.blocksInOrder (K1.noL l d)
          (K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1)) n
    rw [eZ, eG, ← parL_later]
    exact seats_fifty h O hl d
  · subst hL hJ
    have e := numbered_fifty h O hl d
    have hN := firstNo_atPure h hA (K1.place_fifty l hl d)
    rw [eZ] at hN
    rw [show (K1.parL Zp Bs.G₀ l d).place = IM.k1PlaceL l d by cases d <;> rfl, hN, parL_later] at e
    rw [eZ, eG]
    exact e
  · subst hL hJ
    have e := sits_fifty h O hl d
    rw [parL_later] at e
    rw [eZ, eG]
    exact e

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1Seated_two_fill_paid
#print axioms ProofFile.Honest.K1.k1Seated_fifty_fill_paid
