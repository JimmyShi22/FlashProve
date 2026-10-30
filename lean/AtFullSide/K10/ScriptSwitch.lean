-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptSwitch.lean: the closing of a segment (K10): the two ties on the thread's script that the closing's
exchange asks at a message which a code switch has sent (the premises hm and hp of `tab_of_switch` and `fresh_of_switch`,
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieSwitch.lean, XchFreshSwitch.lean), PAID AT THE FIRST CHAIN's SCRIPT OF THE BASE PROVER
(`firstScriptAt`, AtFullSide/K1/FirstScript.lean), in these lemmas' own forms.

  `closingB_is`         the script's closing is the lot's own closing at the plan's layout and segments
  `seat_of_switch`      under the hypothesis: each message of each place of the code switch has a seat q in the plan's list of
                        seats; its number in the witness is `P5J.At.arr` at that seat
  **`pads_of_switch`**    EVERY message n of the sending, kept copies too: `OwnPads` at the seat (q.j, q.t) and the switch's text of
                        the pad
  **`msgs_of_switch`**    a message of which the switch is the first sender (the carrying message; each message behind the kept
                        copies: the next segment's own of moment 0, and the next fold's fresh mask): `OwnMsgs` at the number
                        `P5J.At.arr A.Z q.j q.t` and the switch's text off the pad
  **`ties_of_switch`**    both, at one seat
  `first_carrying`, `first_behind`, `first_last`   which messages these are: number 0; every number above the count of kept copies;
                        the last, where the sending has more messages than kept copies and one

By: `ownMsgs_switch_first`, `joinFit_first`, `switch_in_first` (AtFullSide/K1/FirstScript.lean); `share_pads_fit`, `seats_of_test`
(Johnson/Desc/ProofFile/Honest/K2/JoinShare.lean); `share_seats_at_head` (Honest/K2/Law/JoinShareAtHead.lean); `ownMsgs_off`
(Honest/K2/Law/TabRowsOff.lean).

Limits. AT A KEPT COPY NOTHING IS SAID ON THE MESSAGE: its pad alone. Where a text answers nothing a tie says nothing. That the
state's book seats a member of a closing's group at the seat q is not said here. The hypothesis and the maker's return are
premises. The full size and the older hash alone. No property is claimed.
-/
import AtFullSide.K1.FirstScript
import Johnson.Desc.ProofFile.Honest.K2.Law.JoinShareAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRowsOff
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (firstScriptAt readersB closingB noTree cellsB tokB switchShareB joinFit_first switch_in_first
  ownMsgs_switch_first LocB)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchSent switchSeatIn switchNum switchMsgOff switchPadTxt firstSender
  lotClosingAt segmentsOf)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The script's closing is the lot's own closing at the plan's layout and segments. -/
theorem closingB_is (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    closingB Zq G = lotClosingAt G.first.layout (segmentsOf Zq G) := rfl

/-- **Each message of each place of the code switch has a seat in the plan's list**, and the two defaults of the switch's
share are not read. -/
theorem seat_of_switch (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) {n : Nat} (hn : n < (switchSent p.sizes p.others).size) :
    ∃ q ∈ P5J.At.pseatsAll A.Z, switchSeatIn (P5J.At.pseatsAll A.Z) p.link n = some q ∧
      ((switchSeatIn (P5J.At.pseatsAll A.Z) p.link 0).map (·.j)).getD 0 = q.j ∧
      ((switchSeatIn (P5J.At.pseatsAll A.Z) p.link n).map (·.t)).getD 0 = q.t ∧
      switchNum A.Z p n = P5J.At.arr A.Z q.j q.t := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have ht := K2.Law.share_seats_at_head h.toAtMg O
  rw [← eG] at ht
  obtain ⟨q, hq, e1, e2, e3⟩ := K2.Law.seats_of_test ht hp hn
  refine ⟨q, hq, e1, e2, e3, ?_⟩
  show K2.switchNumIn (P5J.At.pseatsAll A.Z) p.link n = _
  unfold K2.switchNumIn
  rw [e1]
  rfl

/-- **EVERY MESSAGE's PAD**, kept copies too. -/
theorem pads_of_switch (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) {q : P5T.PSeat}
    (hq : switchSeatIn (P5J.At.pseatsAll A.Z) p.link n = some q) :
    OwnPads (firstScriptAt I S Op A cF) Vd q.j q.t (fun k _ => switchPadTxt 0 p n k) := by
  obtain ⟨q', -, e1, e2, e3, -⟩ := seat_of_switch h hA hp hn
  obtain rfl : q' = q := Option.some.inj (e1.symm.trans hq)
  have k := K2.Law.share_pads_fit 0 (K2.coreSender K2.freshTable) (widerRows S A.Z A.G) (readersB I A.Z)
    (closingB A.Z A.G) _ _ _ _ _ _ noTree (joinFit_first h hA) (switch_in_first (I := I) (S := S))
    (cellsB I A.Z) tokB Vd hp hn
  rw [e2, e3] at k
  exact k

/-- **A MESSAGE OF WHICH THE SWITCH IS THE FIRST SENDER**, off its pad, under the plan's number of its seat. -/
theorem msgs_of_switch (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat) {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) (h1 : firstSender p n = true) {q : P5T.PSeat}
    (hq : switchSeatIn (P5J.At.pseatsAll A.Z) p.link n = some q) :
    OwnMsgs (firstScriptAt I S Op A cF) Vd N (P5J.At.arr A.Z q.j q.t)
      (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place))
      (switchMsgOff 0 (widerRows S A.Z A.G) (readersB I A.Z)
        (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) p n) := by
  obtain ⟨q', -, e1, -, -, e4⟩ := seat_of_switch h hA hp hn
  obtain rfl : q' = q := Option.some.inj (e1.symm.trans hq)
  rw [← e4]
  exact K2.Law.ownMsgs_off _ Vd N 0 _ _ _ p _ n _ (ownMsgs_switch_first h hA Vd N hp hn h1)

/-- **BOTH TIES, AT ONE SEAT.** -/
theorem ties_of_switch (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat) {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) (h1 : firstSender p n = true) :
    ∃ q ∈ P5J.At.pseatsAll A.Z, switchSeatIn (P5J.At.pseatsAll A.Z) p.link n = some q ∧
      OwnMsgs (firstScriptAt I S Op A cF) Vd N (P5J.At.arr A.Z q.j q.t)
        (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place))
        (switchMsgOff 0 (widerRows S A.Z A.G) (readersB I A.Z)
          (lotClosingAt A.G.first.layout (segmentsOf A.Z A.G)) p n) ∧
      OwnPads (firstScriptAt I S Op A cF) Vd q.j q.t (fun k _ => switchPadTxt 0 p n k) := by
  obtain ⟨q, hq, e1, -⟩ := seat_of_switch h hA hp hn
  exact ⟨q, hq, e1, msgs_of_switch h hA Vd N hp hn h1 e1, pads_of_switch h hA Vd hp hn e1⟩

/-- The carrying message. -/
theorem first_carrying (p : SwitchPlace) : firstSender p 0 = true := rfl

/-- Each message behind the kept copies. -/
theorem first_behind (p : SwitchPlace) {n : Nat} (hn : p.sizes.target.kept.size < n) : firstSender p n = true := by
  unfold firstSender
  rw [decide_eq_true hn, Bool.or_true]

/-- The last message, where the sending has more messages than kept copies and one. -/
theorem first_last (p : SwitchPlace) (hs : p.sizes.target.kept.size + 1 < (switchSent p.sizes p.others).size) :
    firstSender p ((switchSent p.sizes p.others).size - 1) = true :=
  first_behind p (by omega)

end AtFullSide.K10

#print axioms AtFullSide.K10.closingB_is
#print axioms AtFullSide.K10.seat_of_switch
#print axioms AtFullSide.K10.pads_of_switch
#print axioms AtFullSide.K10.msgs_of_switch
#print axioms AtFullSide.K10.ties_of_switch
#print axioms AtFullSide.K10.first_carrying
#print axioms AtFullSide.K10.first_behind
#print axioms AtFullSide.K10.first_last
