-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ScriptQRaw.lean: CONDITIONAL: THE FIRST OF THE TWO EQUATIONS
THAT THE HONEST SIDE OF AN ATTENTION SEGMENT's OWN ROUNDS (kind K5) SPENDS OF THE SCRIPT
(K5ScriptQ.eMask, Honest/K5/Law/ScriptQ.lean), IN THE SCRIPT's OWN LETTERS: no reader of the
library's is left between Q.msg and the coin. Definitions of propositions, and statements with their
proofs.

  MaskRoom       on public data alone: which member of the list of messages holds the segment's mask
                 row; it has one mask row; the slots and the answers' pads have room in that row
  no_pad5        under MaskRoom no slot below the number of slots is a place of the message's pad
  val_mask       what the witness's messages hold at the address of mask entry number n: the
                 witness's message of that member's number, mask table, row 0, place n
  EMaskRaw       the equation in the Script's own letters
  eMask_iff      **K5ScriptQ.eMask's text holds just if EMaskRaw does**

The premises of eMask_iff, all on public data. The library's test on the seats of mask entries
(masksUpTo, Johnson/Desc/First/Att/K05MasksAtt.lean) says yes up to ns · MaskRoom · each slot under
which a coin of the row lies is below ns. WHOSE THE ROOM IS: ns + ans ≤ the mask code's message
length is the planning program's own test on a segment (linkLaid, OnBytes/Model/StagesLinks.lean),
at THE PLANNER's NUMBER OF SLOTS OF THE BUILT SEGMENT and the request's number of answers. It is a
premise here: no theorem that gives it at any plan is called; that the program's number of entries
of the mask row is that length, and its number of slots this ns, is read so here and typed nowhere.

Limits. The library's test for a pad's place (padB, Johnson/Desc/SeatAt.lean) is typed at one
answer. NO EQUATION IS SHOWN: a form against a form. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ScriptQ
import Johnson.Desc.First.Att.K05MasksAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open Johnson.Pack (pMask)
open VerifiableInference.Desc (Chain padB Wit)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls valAt readAt finOf_some)
open VerifiableInference.Desc.First.Att.P (maskMsg masksUpTo masksUpTo_yes seat_mask)
open VerifiableInference.OnPublicFiles (attMs)
open H2K5.Door (seatAll)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-! ## 1 On public data -/

/-- **The mask row's room.** kM: the number, in the list of messages, of the one that holds the
segment's mask row. ns: the number of slots. ans: the number of answers. It is a definition: a
premise's form, on public data alone. -/
structure MaskRoom (D : Sent) (rad : OnBytes.OracleShape → Nat)
    (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : Nat)
    (hk : kM < (sigListCalls D rad x₁.link).length) (ns ans : Nat) : Prop where
  /-- it is the message with the mask row -/
  isMask : maskMsg D x₁.link = some kM
  /-- it has one mask row -/
  one : ((sigListCalls D rad x₁.link).get ⟨kM, hk⟩).1.maskRows = 1
  /-- there is an answer -/
  ans1 : 1 ≤ ans
  /-- the slots and the answers' pads have room in the row -/
  room : ns + ans ≤ (pMask D.codes ((sigListCalls D rad x₁.link).get ⟨kM, hk⟩).1).ell

/-- **No slot below ns is a place of the pad.** -/
theorem no_pad5 {D : Sent} {rad : OnBytes.OracleShape → Nat}
    {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : Nat}
    {hk : kM < (sigListCalls D rad x₁.link).length} {ns ans : Nat}
    (R : MaskRoom D rad x₁ kM hk ns ans) {n : Nat} (hn : n < ns) :
    padB D.codes ((sigListCalls D rad x₁.link).get ⟨kM, hk⟩).1 true 0 n = false := by
  have h1 := R.ans1
  have h2 : ns + ans ≤ (D.codes.mask.getD
    ((sigListCalls D rad x₁.link).get ⟨kM, hk⟩).1.maskCode default).ell := R.room
  unfold padB
  rw [if_pos rfl, Bool.and_eq_false_iff]
  right
  exact beq_eq_false_iff_ne.2 (by omega)

/-- **What the witness's messages hold at the address of mask entry number n.** CONDITIONAL: the
library's test says yes up to ns; MaskRoom; n is below ns. -/
theorem val_mask {D : Sent} {rad : OnBytes.OracleShape → Nat}
    {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : Nat}
    {hk : kM < (sigListCalls D rad x₁.link).length} {ns ans : Nat}
    (hU : masksUpTo D x₁ ns = true) (R : MaskRoom D rad x₁ kM hk ns ans)
    (seatT : Fin (sigListCalls D rad x₁.link).length → Nat × Nat) (arr : Nat → Nat → Nat)
    {Cw Tok : Type} (w : Wit Cw Tok MsgT) {n : Nat} (hn : n < ns) :
    (valAt D.codes (sigListCalls D rad x₁.link) (seatCalls D x₁.link)
      (attMs x₁ D rad seatT arr w) (.mask n)).getD 0 =
      w.msg (arr (seatT ⟨kM, hk⟩).1 (seatT ⟨kM, hk⟩).2) true 0 n := by
  obtain ⟨-, k, hk', hm, h1, h2⟩ := masksUpTo_yes hU rad
  obtain rfl : kM = k := Option.some.inj (R.isMask.symm.trans hm)
  unfold valAt
  rw [seat_mask hm n]
  show (readAt D.codes (sigListCalls D rad x₁.link) _ ⟨kM, true, 0, n⟩).getD 0 = _
  unfold readAt
  rw [dif_pos hk, if_pos rfl, finOf_some h1, finOf_some (Nat.lt_of_lt_of_le hn h2)]
  show (w.tab D.codes _ _ _ _ true 0 n) = _
  unfold VerifiableInference.Desc.Wit.tab
  rw [no_pad5 R hn]
  rfl

/-! ## 2 The equation in the Script's own letters -/

variable {Z₀ : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z₀ D₀ r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- The number, in the witness, of the message that holds the segment's mask row. -/
noncomputable def maskNo5 (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : Nat)
    (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length) : Nat :=
  h.𝔇.arr (seatAll h x₁ ⟨kM, hk⟩).1 (seatAll h x₁ ⟨kM, hk⟩).2

/-- **The equation in the Script's own letters**: the message of that number holds, in its mask
table, row 0, at the place ν₅ + j, coin number j that the book lends K5's row. It is a definition: a
premise's form. -/
def EMaskRaw (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat)
    (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : Nat)
    (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length) (Z : Seat5) (ν₅ : Nat) : Prop :=
  ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn), Vd v → N ≤ hd.length →
    ∀ j, j < (coins5 Bk k Z).length →
    Q.msg (maskNo5 h x₁ kM hk) k v (hd.take (Q.fixedMsg (maskNo5 h x₁ kM hk))) true 0 (ν₅ + j) =
      Reading.gl.val ((coins5 Bk k Z).getD j zeroE)

variable {h Q}

/-- **K5ScriptQ.eMask's text holds just if the equation in the Script's own letters does.**
CONDITIONAL, on public data alone: see the head. -/
theorem eMask_iff {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat}
    {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : Nat}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z : Seat5} {ν₅ ns ans : Nat}
    (hU : masksUpTo h.𝔇.sent x₁ ns = true) (R : MaskRoom h.𝔇.sent h.𝔇.l3.rad x₁ kM hk ns ans)
    (hin : ∀ (k : Coins Bk) j, j < (coins5 Bk k Z).length → ν₅ + j < ns) :
    (∀ k v hd, Vd v → N ≤ hd.length → ∀ j, j < (coins5 Bk k Z).length →
      (valAt h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link)
        (seatCalls h.𝔇.sent x₁.link)
        (attMs x₁ h.𝔇.sent h.𝔇.l3.rad (seatAll h x₁) h.𝔇.arr (Q.wit k v hd))
        (.mask (ν₅ + j))).getD 0 = Reading.gl.val ((coins5 Bk k Z).getD j zeroE)) ↔
      EMaskRaw h Q Vd N x₁ kM hk Z ν₅ :=
  ⟨fun H k v hd hv hN j hj =>
      (val_mask hU R (seatAll h x₁) h.𝔇.arr (Q.wit k v hd) (hin k j hj)).symm.trans
        (H k v hd hv hN j hj),
    fun H k v hd hv hN j hj =>
      (val_mask hU R (seatAll h x₁) h.𝔇.arr (Q.wit k v hd) (hin k j hj)).trans
        (H k v hd hv hN j hj)⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.no_pad5
#print axioms ProofFile.Honest.K5.val_mask
#print axioms ProofFile.Honest.K5.eMask_iff
