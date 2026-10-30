-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LockRows.lean.
"IT MAY HOLD EMPTILY: hm AND hp ARE PROVED OF NO SCRIPT"; "one run's coins: never quoted for a law".
Its two hypotheses on the Script are premises here, and the ends are equations at
one run's coins: no law on all runs together.

The kind "the code switch" (K2): THE JOIN OF A LATER CLOSING's ROWS WITH THE WITNESS's WORDS, AT ONE
MESSAGE OF A SWITCH's SENDING. A later switch's closing lays the sender's message anew: r. The
verifier's claim at the closed group reads the witness's words at the member's oracle number: wd o.
Where r is the row that the sender's own text lays (hK), and the words are the witness's table at
the message's number and seat (hW), the two agree entry by entry, in the main rows and in the mask
rows. One statement with its proof: a join; no definition.

  `lock_rows_of_key`   the two ends have the form of the second and the third clause of the premise
                       hR of `claimTrue_at_segmentLeft` (Honest/K2/Law/ClaimAtClosing.lean, a
                       file that is not in this library), at one member

THE SPLIT AT `padB` IS SPENT INSIDE, in `tab_rows_switch` (Honest/K2/Law/TabRows.lean): at `padB`'s
places the witness's table is the seat's own pad (`OwnPads`, `padTxt_same`), elsewhere the message
(`OwnMsgs`, `msgTxt_rows`).

WHICH COIN STANDS AT AN ENTRY OF r, BY NUMBER, among the sender's own coins (sent, fresh: the
sender's sending; T := `K1.stepsOf` at the message), each where the text answers and under its law's
own premises. A MASK ROW's ENTRY, row b, place i, of a message n that is not the sending's last: the
coin of the extension field number `maskBase` codes sent fresh n + (b + i * the message's mask
rows): `msgTxt_mask` (Honest/K2/Law/MaskTxt.lean). THE SENDING's LAST MESSAGE, THE FOLD's FRESH
MASK, AT ONE MASK ROW, place q up to 2 k, k the next fold's row variables: the coin of the extension
field number `dueBefore`'s count of that field + `K1.sig` k q; beyond 2 k, below the mask code's
length: 0: `msgTxt_fresh`, `msgTxt_fresh_far` (Honest/K2/Law/FreshTxt.lean, not imported). A PAD's
PLACE IN A MAIN ROW (a sampled message with a main row and no mask row; the last main row, place ell
- T.pad + i, i below T.pad): the coin of the row's own field whose number is that field's count in
`dueBefore` codes sent fresh n, + (T.tails + i): `msgTxt_pad_e`, `msgTxt_pad_f`
(Honest/K2/Law/PadTxt.lean). A MAIN ROW's ENTRY OFF THE PADS' PLACES, BELOW ell, OF AN OWN SAMPLED
MESSAGE: the sender's datum (over the base field: its coordinate 0), no coin: `msgTxt_main_e`,
`msgTxt_main_f` (Honest/K2/Law/MainTxt.lean).

By: `tab_rows_switch`; `K1.rowsMsg`'s own text (Honest/K1/ScriptAt.lean).

Limits. hm and hp: see the first lines; at a Script laid by lots they follow, at a message of which
the switch is the first sender, from "the lot is in the list and agrees there"
(Honest/K2/Law/LotsLaid.lean, not imported); AT A KEPT COPY hm HAS NO SUCH ROAD: this kind lays no
lot of messages there. hK, hW, t1 and t2 are premises: none is paid here. `NoWord` is a premise.
TEXT, NOT MOVE: V is what the sender's text lays at the first fx₀ challenges of hd: that the sender
sent so is not said. At a kept copy in the sending the pad is this switch's, not the original's. AT
A FRESH MASK OF MORE THAN ONE MASK ROW NO LAW NAMES THE COINS OF AN ENTRY: there the ride lays a
coefficient at more than one place. At the kept copies' and the carrying message's main rows off the
pads, and at places from ell on, no law of this kind says what stands. NO LOT IS LAID. Nothing on
any property.
-/
import Johnson.Desc.Means.Says
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Slice (GE)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)

variable {W₀ Rc Xi Tr Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **The later closing's row and the witness's words agree, entry by entry.** -/
theorem lock_rows_of_key (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p₀ : SwitchPlace)
    (fx₀ n num j t : Nat)
    (hm : OwnMsgs Q Vd N num fx₀ (switchMsgTxt ch D readers closing p₀ n))
    (hp : OwnPads Q Vd j t (fun k _ => switchPadTxt ch p₀ n k))
    (hw : NoWord (switchSent p₀.sizes p₀.others)) (hn : n < (switchSent p₀.sizes p₀.others).size)
    (k : Coins Bk) {c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries}
    (hH : handed ch p₀ k = some c₀) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hd : List Fmt.Drawn)
    (hN : N ≤ hd.length) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p₀ c₀ w (hd.take fx₀) = .ok V)
    -- THE KEY's END (key_of_lots: R.rows[n]? = some (V n) | R.fresh = some (V (size - 1)))
    {r : Johnson.Prover.Send.Rows} (hK : r = V n)
    -- (T1) · (T2)
    {codes : OnBytes.Codes} {sh : OnBytes.OracleShape} (t1 : codes = p₀.sizes.codes)
    (t2 : sh = ((switchSent p₀.sizes p₀.others).getD n default).shape)
    -- THE LOCK's WORD (link_ | head_ | fin_word_front at v := Q.wit k w hd; (T3) inside num, j, t)
    (wd : Words GE) (o : Nat)
    (hW : ∀ part b i, b < sh.rows part →
      wd o part (b + i * 2 ^ ceilLog2 (sh.rows part)) =
        (Q.wit k w hd).tab codes sh num j t (part == .mask) b i) :
    (∀ b i, b < sh.mainRows →
      r.main (sh.mainDeg == 3) b i = wd o .main (b + i * 2 ^ ceilLog2 sh.mainRows)) ∧
    (∀ b i, b < sh.maskRows → r.mask b i = wd o .mask (b + i * 2 ^ ceilLog2 sh.maskRows)) := by
  subst hK t1 t2
  have e := tab_rows_switch Q Vd N ch D readers closing p₀ fx₀ n num j t hm hp hw hn k hH w hv hd
    hN hV
  refine ⟨fun b i hb => ?_, fun b i hb => ?_⟩
  · exact ((hW .main b i hb).trans (congrFun (congrFun (congrFun e false) b) i)).symm
  · exact ((hW .mask b i hb).trans (congrFun (congrFun (congrFun e true) b) i)).symm

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lock_rows_of_key
