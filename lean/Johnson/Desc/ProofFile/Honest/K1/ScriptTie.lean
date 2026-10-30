-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/ScriptTie.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: UNDER THE TIE, THE WITNESS's TABLE OF A MESSAGE OF THIS KIND's, READ BY THE
LIBRARY's ONE ACCESSOR, IS THE ROWS THAT THE PART LAYS. Statements and proofs; no definition.

THE TIE: two hypotheses on a Script Q, in the threads' own forms (OwnMsgs, OwnPads:
Honest/Thread/ScriptLots.lean), at K1's lots' texts (msgTxt, padTxt: Honest/K1/ScriptLots.lean): at
the witness's own number "num" of the place's message number n and at its seat (tree j, tenant t).

  tab_rows      where the part's cut off the run's coins is c, at an input that Vd admits and a list
                of at least N challenges: (Q.wit k w hd).tab ... num j t (Wit.tab,
                Johnson/Desc/Sound/MsgSig.lean) = rowsMsg of rowsLaid at c, at the first "front"
                challenges
  tab_rows_covers   THE SAME UNDER THE NAMED PUBLIC PREMISE bookCovers, at the first or the shared
                chain: there is such a cut, and the table is the rows at it

Limits. THE TWO HYPOTHESES ARE PROVED OF NO SCRIPT HERE. AT A Vd THAT HOLDS OF NO INPUT THEY ASK
NOTHING AND EVERY SCRIPT MEETS THEM; AT A BOOK THAT IS SHORT AT THE PART's ADDRESS msgTxt AND padTxt
ANSWER NOTHING AND EVERY SCRIPT MEETS THEM: so tab_rows has the cut, and tab_rows_covers the public
test, as a premise by name. That num is the number at which a pin reads the witness (arr at the
seat) is not said here; nor that front is the thread's front and the rounds in front of the member;
at N < front the text is read at a shorter list than it is meant for: to nail N, front and Vd is the
matter of the record K1Seated (Honest/K1/Seated.lean). TWO MODULES BEAR THE LAST NAME ScriptLots:
the threads' (Honest/Thread/) and this kind's (Honest/K1/). An equation at each value of the coins:
no sentence on what a coin, a pad or a mask row is for. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {W Wl X Cells Tok : Type}

/-- **Under the tie the witness's table, read by the one accessor, is the rows.** -/
theorem tab_rows (Q : Script Bk Wl Cells Tok MsgT) (Vd : Wl → Prop) (N : Nat) (ch : Nat)
    (wit : Wl → W) (J : SendJob W X) (own₀ : X) (front n num j t : Nat)
    (hm : OwnMsgs Q Vd N num front (msgTxt ch wit J own₀ n))
    (hp : OwnPads Q Vd j t (fun k _ => padTxt ch J n k))
    (k : Coins Bk) (c : Cs (dueR J.P J.ride))
    (hc : lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c)
    (w : Wl) (hw : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length) :
    (Q.wit k w hd).tab J.P.codes (shapeAt J.P n) num j t =
      rowsMsg (shapeAt J.P n) (rowsLaid J own₀ c (wit w) (hd.take front) n) := by
  funext mask r i
  unfold Wit.tab
  by_cases hb : padB J.P.codes (shapeAt J.P n) mask r i = true
  · rw [if_pos hb]
    have e := hp k w hw mask r i _ (padTxt_some ch J n k c hc mask r i hb)
    show Q.pad j t k w mask r i = _
    rw [e, pad_same J own₀ n c (wit w) (hd.take front) mask r i hb]
    rfl
  · rw [if_neg hb]
    have e := hm k w hd hw hN mask r i _
      (msgTxt_some ch wit J own₀ n k c hc w (hd.take front) mask r i)
    show Q.msg num k w (hd.take (Q.fixedMsg num)) mask r i = _
    rw [e]
    rfl

/-- **The same under the named public premise.** -/
theorem tab_rows_covers (Q : Script Bk Wl Cells Tok MsgT) (Vd : Wl → Prop) (N : Nat) (ch : Nat)
    (hch : ch ≤ 1) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (front n num j t : Nat)
    (hb : bookCovers Bk ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) = true)
    (hm : OwnMsgs Q Vd N num front (msgTxt ch wit J own₀ n))
    (hp : OwnPads Q Vd j t (fun k _ => padTxt ch J n k))
    (k : Coins Bk) (w : Wl) (hw : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length) :
    ∃ c, lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c ∧
      (Q.wit k w hd).tab J.P.codes (shapeAt J.P n) num j t =
        rowsMsg (shapeAt J.P n) (rowsLaid J own₀ c (wit w) (hd.take front) n) := by
  have h1 := lentCut_isSome k ch hch ⟨J.P.place, 0⟩ (dueR J.P J.ride)
  rw [hb] at h1
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h1
  exact ⟨c, hc, tab_rows Q Vd N ch wit J own₀ front n num j t hm hp k c hc w hw hd hN⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tab_rows
#print axioms ProofFile.Honest.K1.tab_rows_covers
