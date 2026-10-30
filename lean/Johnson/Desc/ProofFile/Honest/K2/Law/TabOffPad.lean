-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/TabOffPad.lean: the kind "the code switch" (K2): THE WITNESS's
TABLE AT AN ENTRY OFF THE PAD, UNDER THE TIE ON THE SCRIPT's MESSAGE ALONE: where the test `padB`
says no at (mask, r, i), the table that the one accessor `Wit.tab` reads at a switch's message is
the entry of the rows that the switch lays. The sister of `tab_rows_off`
(Honest/K2/Law/TabRowsOff.lean), which has the whole table and asks the pad's tie too. One statement
with its proof; no definition.

  `tab_off_pad`   THE END

By: the second arm of `tab_rows_off`'s own proof: `msgTxt_rows` (Honest/K2/Law/MainTxt.lean);
`Wit.tab` and `switchMsgOff` (Honest/K2/MsgOff.lean) unfolded at hb. GONE, against `tab_rows_off`:
the pad's tie hp · hw · hn. The seat's two letters j, t are free: off the pad `Wit.tab` does not
read them. Kin, not called: `first_lays_off_padB` (Honest/K1/FirstOffPad.lean),
`later_lays_off_padB` (Honest/K1/LaterOffPad.lean), of other authors: by our reader's reading of
their statements (not the author's): public laws at the shared sending whose ends have hb's form,
`padB … = false`: of a sort that could pay hb there.

Limits. hm IS A TIE TO A SCRIPT: a premise: no Script is laid. hH AND hV ARE PREMISES: that the
switch is handed its stretches, and that its rows are laid at what was heard up to fx. ONE ENTRY,
OFF THE PAD: at a pad's place nothing is said. n IS ANY NUMBER: past the last message of the sending
`getD` hands the default notice, and both sides are read at its shape. It stands behind no step and
no yes of a verifier. An equation at one run's coins: what is WRITTEN where. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRowsOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB Wit)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script OwnMsgs)

variable {W₀ Rc Xi Tr Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **Off the pad, under the tie on the Script's message alone, the witness's table is the
rows.** -/
theorem tab_off_pad (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    (fx n num j t : Nat) (hm : OwnMsgs Q Vd N num fx (switchMsgOff ch D readers closing p n))
    (k : Coins Bk) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hd : List Fmt.Drawn)
    (hN : N ≤ hd.length) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w (hd.take fx) = .ok V) (mask : Bool) (r i : Nat)
    (hb : padB p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape mask r i =
      false) :
    (Q.wit k w hd).tab p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape num j t
        mask r i =
      K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) mask r i := by
  have hy := msgTxt_rows ch D readers closing p n k w (hd.take fx) hH hV mask r i
  have hb' : ¬ padB p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape mask r
      i = true := by
    rw [hb]
    exact Bool.false_ne_true
  unfold Wit.tab
  rw [if_neg hb']
  refine hm k w hd hv hN mask r i _ ?_
  unfold switchMsgOff
  rw [if_neg hb']
  exact hy

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.tab_off_pad
