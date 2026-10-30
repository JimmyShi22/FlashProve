-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LockRowsShared.lean. IT MAY HOLD EMPTILY: hm AND hp ARE PROVED
OF NO SCRIPT HERE. One run's coins: never quoted for a law.

The kind "the code switch" (K2): THE JOIN OF A LATER CLOSING's ROWS WITH THE WITNESS's WORDS, AT ONE
MESSAGE THAT A SENDER OF THE SHARED SENDING's KIND (K1) SENT: the sister of `lock_rows_of_key`
(LockRows.lean of this folder), which stands at a switch's own sending. A switch's closing lays the
sender's message anew: r. The verifier's claim at the closed group reads the witness's words at the
member's oracle number: wd o. Where r is the row that the sender's own text lays (hK), and the words
are the witness's table at the message's number and seat (hW), the two agree entry by entry, in the
main rows and in the mask rows. One statement with its proof: a join; no definition.

  `lock_rows_of_shared`   the two ends have the form of the clauses on a member's main and mask
                       entries in `LockAsks` (ClaimOfLock.lean of this folder), at one member

By: `K1.tab_rows` (Honest/K1/ScriptTie.lean, of other authors): under the Script's two ties the
witness's table is the rows; `K1.rowsMsg`'s own text (Honest/K1/ScriptAt.lean). THE NEAREST KIN, OF
OTHER AUTHORS, AND ONE STEP FURTHER: `words_at` (Honest/K1/Law/WordsAtFour.lean): by the same hinge,
under the record `K1Seated` and four public facts: `wordsFirst` itself against `rowsLaid`: so hW is
paid there; its elder at the member's own step: `words_behind` (Honest/K1/Law/ExchangeAtPins.lean).
Kin: `first_fresh_clause` (FreshClauseFirst.lean of this folder) spends the same hinge at the first
segment's fresh mask.

Limits. hm AND hp, the Script's two ties at the sender's texts, ARE PREMISES. hK IS A PREMISE: that
the closing's row is `K1.rowsLaid` at the sender's own coins: `copyShared_first_at_head`,
`copyShared_later_at_head` (CopySharedAtHead.lean of this folder) end in `K1.rowsR` at data that are
a letter there: that these are the job's own data is not said here. hW, t1 and t2 are premises. ho:
the sender's cut is there: a premise. TEXT, NOT MOVE: what the sender's text lays at the first
"front" challenges of hd: that the sender sent so is not said. WHAT IT WOULD PAY: the two limbs of
`LockAsks` on the members' entries, at the messages of senders of the kind K1: no law calls it. NO
LOT IS LAID. NOT IN FRONT OF A LAW OVER COINS. Nothing on any property.
-/
import Johnson.Desc.Means.Says
import Johnson.Desc.ProofFile.Honest.K1.ScriptTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Slice (GE)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open Johnson.Prover.Send (shapeAt)

variable {Wl W X Cells Tok : Type} {Bk : ProverCoinCounts}

/-- hm, hp, ho, hK AND hW ARE PREMISES. **The later closing's row and the witness's words agree,
entry by entry, at a message of a sender of the kind K1.** One run's coins: never quoted for a law.
-/
theorem lock_rows_of_shared (Q : Script Bk Wl Cells Tok MsgT) (Vd : Wl → Prop) (N ch : Nat)
    (wit : Wl → W) (J : K1.SendJob W X) (own₀ : X) (front n num j t : Nat)
    (hm : OwnMsgs Q Vd N num front (K1.msgTxt ch wit J own₀ n))
    (hp : OwnPads Q Vd j t (fun k _ => K1.padTxt ch J n k))
    (k : Coins Bk) {cs : Cs (K1.dueR J.P J.ride)}
    (ho : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some cs)
    (w : Wl) (hv : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length)
    {r : Johnson.Prover.Send.Rows} (hK : r = K1.rowsLaid J own₀ cs (wit w) (hd.take front) n)
    {codes : OnBytes.Codes} {sh : OnBytes.OracleShape} (t1 : codes = J.P.codes)
    (t2 : sh = shapeAt J.P n) (wd : Words GE) (o : Nat)
    (hW : ∀ part b i, b < sh.rows part →
      wd o part (b + i * 2 ^ ceilLog2 (sh.rows part)) =
        (Q.wit k w hd).tab codes sh num j t (part == .mask) b i) :
    (∀ b i, b < sh.mainRows →
      r.main (sh.mainDeg == 3) b i = wd o .main (b + i * 2 ^ ceilLog2 sh.mainRows)) ∧
    (∀ b i, b < sh.maskRows → r.mask b i = wd o .mask (b + i * 2 ^ ceilLog2 sh.maskRows)) := by
  subst hK t1 t2
  have e := K1.tab_rows Q Vd N ch wit J own₀ front n num j t hm hp k cs ho w hv hd hN
  refine ⟨fun b i hb => ?_, fun b i hb => ?_⟩
  · exact ((hW .main b i hb).trans (congrFun (congrFun (congrFun e false) b) i)).symm
  · exact ((hW .mask b i hb).trans (congrFun (congrFun (congrFun e true) b) i)).symm

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lock_rows_of_shared
