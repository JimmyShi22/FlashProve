-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/TabRows.lean: the kind "the code switch" (K2): UNDER THE TIE,
THE WITNESS's TABLE OF A MESSAGE OF A SWITCH's SENDING, READ BY THE LIBRARY's ONE ACCESSOR
(`Wit.tab`, Johnson/Desc/Sound/MsgSig.lean), IS THE ROWS THAT THE SWITCH LAID: the sister of the
shared sending's `tab_rows` (Honest/K1/ScriptTie.lean, of other authors), whose proof it follows
step by step. One statement with its proof: a join; no definition.

THE TIE: two hypotheses on a Script Q, in the threads' own forms (`OwnMsgs`, `OwnPads`,
Honest/Thread/ScriptLots.lean), at this kind's lots' texts (`switchMsgTxt`, `switchPadTxt`,
Honest/K2/ScriptLots.lean): at the witness's own number num of the sending's message number n, and
at its seat (tree j, tenant t).

  `tab_rows_switch`   where the part is handed c, and the rows are laid at the first fx challenges:
                      (Q.wit k w hd).tab ... num j t = `K1.rowsMsg` of V n: an equation of functions

By: off `padB`'s places `OwnMsgs` and `msgTxt_rows` (Honest/K2/Law/MainTxt.lean); at them `OwnPads`
and `padTxt_same` (Honest/K2/Law/PadSame.lean).

Limits. THE TWO HYPOTHESES ARE PROVED OF NO SCRIPT. At a Vd that holds of no input they ask nothing
and every Script meets them; where the texts do not answer they ask nothing: so that the part is
handed c, and that the rows are laid, are premises by name. `NoWord` is a premise. That num is the
number at which a pin reads the witness, that (j, t) is the message's seat, that fx is the number of
challenges in front of the sender's part: not said here. At N below fx the text is read at a shorter
list than it is meant for. AT A KEPT COPY IN THE SENDING the table's pad is this switch's, not the
original's. An equation at each run's coins: what is WRITTEN where. NO LOT IS LAID. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PadSame
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB Wit)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)

variable {W₀ Rc Xi Tr Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **Under the tie the witness's table, read by the one accessor, is the rows.** -/
theorem tab_rows_switch (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    (fx n num j t : Nat) (hm : OwnMsgs Q Vd N num fx (switchMsgTxt ch D readers closing p n))
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
    exact hm k w hd hv hN mask r i _ hy

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.tab_rows_switch
