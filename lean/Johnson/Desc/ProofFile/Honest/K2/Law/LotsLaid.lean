-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LotsLaid.lean: the kind "the code switch" (K2): THE TIE AT A
SCRIPT LAID BY LOTS: at the threads' `Script.ofLots` (Honest/Thread/ScriptLots.lean):
IF A LOT OF THIS KIND's (`switchMsgLots`, `switchPadLots`, Honest/K2/ScriptLots.lean) LIES
IN THE LAID LIST AND AGREES THERE, the laying meets the threads' form (`OwnMsgs`, `OwnPads`) at this
kind's text: the two hypotheses of `tab_rows_switch` (Honest/K2/Law/TabRows.lean). After the form of
the shared sending's `msgs_of_lots` and `pads_of_lots` (Honest/K1/LotsLaid.lean).
Statements with their proofs: calls; no definition.

  `msgLot_mem`, `padLot_mem`   which lots stand in this kind's two lists
  `ownMsgs_of_lots`   A MESSAGE OF WHICH THE SWITCH IS THE FIRST SENDER: `OwnMsgs` at `switchMsgTxt`
  `ownPads_of_lots`   ANY MESSAGE OF THE SENDING: `OwnPads` at `switchPadTxt`
  `hin_switchMsgs_of_agree`, `hin_switchPads_of_agree`   this kind's list lies in the laid list, and
                      the whole list agrees: then each of its lots lies in and agrees
  `tab_rows_of_lots`  so, at such a laying, the end of `tab_rows_switch`

AT A KEPT COPY (n from 1 to the number of kept members) NOTHING IS SAID ON THE MESSAGE:
`switchMsgLots` lays no lot there (`firstSender`): all copies share the message's number, and at
that number another sender's lot is meant to stand. So `ownMsgs_of_lots` and `tab_rows_of_lots` ask
`firstSender p n = true`. The pads' lots stand at every message.

By: `ofLots_ownMsgs`, `ofLots_ownPads` (Honest/Thread/ScriptLots.lean).

Limits. NO SCRIPT IS LAID; NO LIST IS NAMED. ONE PREMISE IS TRADED FOR ANOTHER: that a lot of this
kind's is a member of the laid list and agrees with the list's other lots at its number is shown
here of no list. A lot that answers nothing agrees with everything: where the part is handed
nothing, or the closing refuses, both ends hold idly. num, tree, tenant and fx are letters: this
kind's lots at the plan's own letters (num := `switchNum`, the tree and tenant of the seat that
`switchSeatIn` finds, fx := the challenges in front of the switch's member) are written in
Honest/K2/JoinShare.lean (`switchShareAt`), which stands above this file. That a number of this
kind's lots never meets another kind's lot's number is not said here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script MsgLot PadLot TreeLot OwnMsgs OwnPads LotsAgree PadLotsAgree
  MsgsAgree PadsAgree ofLots_ownMsgs ofLots_ownPads)

variable {W₀ Rc Xi Tr S Cl Cells Tok : Type} {Bk : ProverCoinCounts}

/-- Which lots of messages stand in this kind's list. -/
theorem msgLot_mem (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (num : Nat → Nat) (fx : Nat) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) (h1 : firstSender p n = true) :
    (⟨num n, fx, switchMsgTxt ch D readers closing p n⟩ : MsgLot Bk (Local W₀ Rc Xi Tr)) ∈
      switchMsgLots ch D readers closing p num fx :=
  List.mem_map.2 ⟨n, List.mem_filter.2 ⟨List.mem_range.2 hn, h1⟩, rfl⟩

/-- Which lots of pads stand in this kind's list. -/
theorem padLot_mem (ch : Nat) (p : SwitchPlace) (tree : Nat) (tenant : Nat → Nat) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) :
    (⟨tree, tenant n, fun k _ => switchPadTxt ch p n k⟩ : PadLot Bk (Local W₀ Rc Xi Tr)) ∈
      switchPadLots ch p tree tenant :=
  List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩

variable (bs : List (Block S Cl)) (front : Nat) (cells : Local W₀ Rc Xi Tr → Cells)
  (tok : Local W₀ Rc Xi Tr → Tok) (pl : List (PadLot Bk (Local W₀ Rc Xi Tr)))
  (tl : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) (ml : List (MsgLot Bk (Local W₀ Rc Xi Tr)))

/-- **A MESSAGE.** The lot lies in the laid list and agrees there. -/
theorem ownMsgs_of_lots (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (num : Nat → Nat) (fx n : Nat)
    (hin : (⟨num n, fx, switchMsgTxt ch D readers closing p n⟩ : MsgLot Bk _) ∈ ml ∧
      LotsAgree ml ⟨num n, fx, switchMsgTxt ch D readers closing p n⟩)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat) :
    OwnMsgs (Script.ofLots bs front cells tok pl tl ml) Vd N (num n) fx
      (switchMsgTxt ch D readers closing p n) :=
  ofLots_ownMsgs bs front cells tok pl tl ml hin.1 hin.2 Vd N

/-- **A PAD.** The lot lies in the laid list and agrees there. -/
theorem ownPads_of_lots (ch : Nat) (p : SwitchPlace) (tree : Nat) (tenant : Nat → Nat) (n : Nat)
    (hin : (⟨tree, tenant n, fun k _ => switchPadTxt ch p n k⟩ : PadLot Bk _) ∈ pl ∧
      PadLotsAgree pl ⟨tree, tenant n, fun k _ => switchPadTxt ch p n k⟩)
    (Vd : Local W₀ Rc Xi Tr → Prop) :
    OwnPads (Script.ofLots bs front cells tok pl tl ml) Vd tree (tenant n)
      (fun k _ => switchPadTxt ch p n k) :=
  ofLots_ownPads bs front cells tok pl tl ml hin.1 hin.2 Vd

/-- This kind's list lies in the laid list, and the whole list agrees. -/
theorem hin_switchMsgs_of_agree (ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    (num : Nat → Nat) (fx : Nat)
    (hsub : ∀ L ∈ switchMsgLots ch D readers closing p num fx, L ∈ ml) (ha : MsgsAgree ml)
    {n : Nat} (hn : n < (switchSent p.sizes p.others).size) (h1 : firstSender p n = true) :
    (⟨num n, fx, switchMsgTxt ch D readers closing p n⟩ : MsgLot Bk _) ∈ ml ∧
      LotsAgree ml ⟨num n, fx, switchMsgTxt ch D readers closing p n⟩ :=
  have m := hsub _ (msgLot_mem ch D readers closing p num fx hn h1)
  ⟨m, ha _ m⟩

/-- The like for the pads, at every message. -/
theorem hin_switchPads_of_agree (ch : Nat) (p : SwitchPlace) (tree : Nat) (tenant : Nat → Nat)
    (hsub : ∀ L ∈ switchPadLots ch p tree tenant, L ∈ pl) (ha : PadsAgree pl) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) :
    (⟨tree, tenant n, fun k _ => switchPadTxt ch p n k⟩ : PadLot Bk _) ∈ pl ∧
      PadLotsAgree pl ⟨tree, tenant n, fun k _ => switchPadTxt ch p n k⟩ :=
  have m := hsub _ (padLot_mem ch p tree tenant hn)
  ⟨m, ha _ m⟩

/-- **At such a laying, the end of `tab_rows_switch`.** -/
theorem tab_rows_of_lots (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (num : Nat → Nat) (fx tree : Nat)
    (tenant : Nat → Nat)
    (hsm : ∀ L ∈ switchMsgLots ch D readers closing p num fx, L ∈ ml) (ham : MsgsAgree ml)
    (hsp : ∀ L ∈ switchPadLots ch p tree tenant, L ∈ pl) (hap : PadsAgree pl)
    (hw : NoWord (switchSent p.sizes p.others)) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size)
    (h1 : firstSender p n = true) (k : Coins Bk)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : handed ch p k = some c)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w (hd.take fx) = .ok V) :
    ((Script.ofLots bs front cells tok pl tl ml).wit k w hd).tab p.sizes.codes
        ((switchSent p.sizes p.others).getD n default).shape (num n) tree (tenant n) =
      K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) :=
  tab_rows_switch _ (fun _ => True) 0 ch D readers closing p fx n (num n) tree (tenant n)
    (ownMsgs_of_lots bs front cells tok pl tl ml ch D readers closing p num fx n
      (hin_switchMsgs_of_agree ml ch D readers closing p num fx hsm ham hn h1) _ _)
    (ownPads_of_lots bs front cells tok pl tl ml ch p tree tenant n
      (hin_switchPads_of_agree pl ch p tree tenant hsp hap hn) _)
    hw hn k hH w trivial hd (Nat.zero_le _) hV

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.msgLot_mem
#print axioms ProofFile.Honest.K2.Law.padLot_mem
#print axioms ProofFile.Honest.K2.Law.ownMsgs_of_lots
#print axioms ProofFile.Honest.K2.Law.ownPads_of_lots
#print axioms ProofFile.Honest.K2.Law.hin_switchMsgs_of_agree
#print axioms ProofFile.Honest.K2.Law.hin_switchPads_of_agree
#print axioms ProofFile.Honest.K2.Law.tab_rows_of_lots
