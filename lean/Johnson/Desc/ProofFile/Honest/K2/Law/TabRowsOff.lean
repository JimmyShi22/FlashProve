-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/TabRowsOff.lean: the kind "the code switch" (K2):
`tab_rows_switch` (Honest/K2/Law/TabRows.lean) UNDER A WEAKER TIE: the Script's message is asked to
be the kind's text OFF THE PAD alone (`switchMsgOff`, Honest/K2/MsgOff.lean). Under that tie and the
pad's, the witness's table is the rows. Two statements with their proofs; no definition.

  `ownMsgs_off`   the whole text's tie gives the tie off the pad
  `tab_rows_off`  THE END

By: `msgTxt_rows`, `padTxt_same` (Honest/K2/Law/PadSame.lean and beneath); the second proof is
`tab_rows_switch`'s own, which spends its tie on the message only where `padB` says no.

Limits. BOTH TIES ARE PREMISES: shown at no Script here. hH AND hV ARE PREMISES: that the switch is
handed its coins, and that its rows are laid. hw: no message has main rows and no sample. At one
run's coins. It says which table the witness has at a seat: nothing on what it holds. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRows
import Johnson.Desc.ProofFile.Honest.K2.MsgOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB Wit)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)

variable {W₀ Rc Xi Tr Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **The whole text's tie gives the tie off the pad.** -/
theorem ownMsgs_off (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    (fx n num : Nat) (hm : OwnMsgs Q Vd N num fx (switchMsgTxt ch D readers closing p n)) :
    OwnMsgs Q Vd N num fx (switchMsgOff ch D readers closing p n) := by
  intro k w hd hv hN mask r i y hy
  unfold switchMsgOff at hy
  split at hy
  · cases hy
  · exact hm k w hd hv hN mask r i y hy

/-- **Under the tie off the pad, and the pad's, the witness's table is the rows.** -/
theorem tab_rows_off (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    (fx n num j t : Nat) (hm : OwnMsgs Q Vd N num fx (switchMsgOff ch D readers closing p n))
    (hp : OwnPads Q Vd j t (fun k _ => switchPadTxt ch p n k))
    (hw : NoWord (switchSent p.sizes p.others)) (hn : n < (switchSent p.sizes p.others).size)
    (k : Coins Bk) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hd : List Fmt.Drawn)
    (hN : N ≤ hd.length) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w (hd.take fx) = .ok V) :
    (Q.wit k w hd).tab p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape num j t =
      K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) := by
  funext mask r i
  have hy := msgTxt_rows ch D readers closing p n k w (hd.take fx) hH hV mask r i
  unfold Wit.tab
  by_cases hb : padB p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape mask r
      i = true
  · rw [if_pos hb]
    exact hp k w hv mask r i _ (padTxt_same ch D readers closing p k w (hd.take fx) hw hn hb hy)
  · rw [if_neg hb]
    refine hm k w hd hv hN mask r i _ ?_
    unfold switchMsgOff
    rw [if_neg hb]
    exact hy

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.ownMsgs_off
#print axioms ProofFile.Honest.K2.Law.tab_rows_off
