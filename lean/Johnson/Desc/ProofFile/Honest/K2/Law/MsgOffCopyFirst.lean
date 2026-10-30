-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MsgOffCopyFirst.lean: the kind "the code switch" (K2): WHEREVER
THE TEXT OFF THE PAD OF A KEPT COPY AT THE FIRST SWITCH ANSWERS, THE SHARED SENDING's OWN TEXT
ANSWERS THE SAME: at one run: p: a switch with just one segment in front; J: a job of the kind K1;
n: a message of J's: for every (mask, r, j) and y: if `switchMsgOff` (Honest/K2/MsgOff.lean) at p's
message 1 + i answers y, so does `K1.msgTxt` (Honest/K1/ScriptLots.lean) at J's message n. AT EVERY
PLACE, not in range alone. The sister of `msgOff_copy_is_senders` (MsgOffCopy.lean of this folder),
whose sender is a switch. Over the base field; where the two messages have one shape, with no mask
row and one answer, and the two plans one list of codes. Lemmas and one statement with its proof: a
split in four; no definition.

  `rowsR_mask_bare`   a message of the shared sending with no mask row and no riding table has
                    zeros for mask entries
  `rowsR_main_beyond`   beyond its rows or the code's length its main entries over the base field
                    are zeros
  `msgOff_copy_is_firsts`   THE END

The four: AT THE PAD the copy's text answers nothing · A MASK ENTRY: zero at both:
`msgTxt_mask_bare` (TxtBeyond.lean) · A MAIN ENTRY BEYOND THE RANGES: one value at both:
`msgTxt_beyond` (there) · A MAIN ENTRY IN RANGE, OFF THE PAD: the copy's text is the closing's kept
entry (`msgTxt_copy_f`, CopyTxt.lean); that is an entry of the rows that the closing has laid anew
of the one segment in front (`kept_at_closing`, KeptAtClosing.lean, at no segment in front of that
one); these rows are the sender's own: hrows, A PREMISE.

The two small laws: `rowsR_main_beyond`: zeros from the code's length on, at the base field's
entries, and beyond the rows; `rowsR_mask_bare`: no mask row, no riding table. Kin, none a twin by
its statement, in the library: `other_field`, `no_other_ride` (Honest/K1/NoOther.lean): the other
field's tables hold 0; a riding table of one row.

Limits. ONE RUN: k, w and the two lists of challenges are letters: a tie on a Script's message
(`OwnMsgs`) runs over all of them: that step is not taken here. hrows IS A PREMISE: that the rows
laid anew of the first segment have, at the kept member's number, in range, the main entries over
the base field of the rows that J lays of its own coins; with it, which shapes the group keeps.
hcut: the sender's own coins are there. hH, hV: the switch is handed its stretches and lays its
rows. PUBLIC, not paid here: hA · hw · hi · hn · h3 · hbare · ha1 · hm · hpad · hs · hc · hride ·
hell. What is WRITTEN where, at one run's coins: no sentence on what an element is for. NO LOT IS
LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.KeptAtClosing
import Johnson.Desc.ProofFile.Honest.K2.Law.TxtBeyond
import Johnson.Desc.ProofFile.Honest.K2.Law.PadPlaces
import Johnson.Desc.ProofFile.Honest.K2.MsgOff
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.K2.Honest (Left zeroG)
open Johnson.Prover.Send (shapeAt)

/-- A message with no mask row and no riding table has zeros for mask entries. -/
theorem rowsR_mask_bare (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs (K1.dueR P ride)) (n : Nat)
    (hr : ride n = none) (hb : (shapeAt P n).maskRows = 0) (r j : Nat) :
    (K1.rowsR P ride data c n).mask r j = 0 := by
  show (match ride n with
    | some R => if r < (shapeAt P n).maskRows ∧ j < _ then _ else 0
    | none => if r < (shapeAt P n).maskRows ∧ j < _ then _ else 0) = (0 : Cb.Gl.E)
  rw [hr, hb]
  exact if_neg fun q => Nat.not_lt_zero _ q.1

/-- Beyond its rows or the code's length the main entries over the base field are zeros. -/
theorem rowsR_main_beyond (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs (K1.dueR P ride)) (n : Nat)
    {r j : Nat}
    (ho : (decide (r < (shapeAt P n).mainRows) &&
      decide (j < (P.codes.base.getD (shapeAt P n).code default).ell)) = false) :
    (K1.rowsR P ride data c n).mainF r j = 0 := by
  have hq : ((shapeAt P n).mainDeg == 3 || decide ((shapeAt P n).mainRows ≤ r) ||
      decide ((P.codes.base.getD (shapeAt P n).code default).ell ≤ j)) = true := by
    rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not] at ho
    rw [Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    rcases ho with q | q
    · exact Or.inl (Or.inr (Nat.le_of_not_lt q))
    · exact Or.inr (Nat.le_of_not_lt q)
  show (if ((shapeAt P n).mainDeg == 3 || decide ((shapeAt P n).mainRows ≤ r) ||
      decide ((P.codes.base.getD (shapeAt P n).code default).ell ≤ j)) = true then 0 else _) =
    (0 : Cb.Gl.F)
  rw [if_pos hq]

variable {W₀ Rc Xi Tr Wk X : Type} {Bk : ProverCoinCounts}

/-- **WHEREVER THE KEPT COPY's TEXT OFF THE PAD ANSWERS, THE SHARED SENDING's OWN TEXT ANSWERS THE
SAME.** hrows IS A PREMISE. One run. -/
theorem msgOff_copy_is_firsts (ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) {lay : OnBytes.Params.ReqLayout}
    {segs : List SegmentPub} (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd hd' : List Fmt.Drawn)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : handed ch p k = some c)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt lay segs) p c w hd = .ok V)
    {Sg : SegmentPub} (hA : segs.take p.link = [Sg])
    (hw : NoWord (switchSent p.sizes p.others)) {i n : Nat} (hi : i < p.sizes.kept.length)
    (hn : 1 + i < (switchSent p.sizes p.others).size)
    (h3 : (((switchSent p.sizes p.others).getD (1 + i) default).shape.mainDeg == 3) = false)
    (hbare : ((switchSent p.sizes p.others).getD (1 + i) default).shape.maskRows = 0)
    (ha1 : ((switchSent p.sizes p.others).getD (1 + i) default).shape.answers = 1)
    (hm : 0 < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows)
    (hpad : (K1.stepsOf p.sizes.codes ((switchSent p.sizes p.others).getD (1 + i) default).shape
      none).pad ≤ (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell)
    (wit : Local W₀ Rc Xi Tr → Wk) (J : K1.SendJob Wk X) (own₀ : X)
    {cs : Cs (K1.dueR J.P J.ride)}
    (hcut : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some cs)
    (hs : shapeAt J.P n = ((switchSent p.sizes p.others).getD (1 + i) default).shape)
    (hc : J.P.codes = p.sizes.codes) (hride : J.ride n = none)
    (hell : (Sg.sizes.codes.base.getD Sg.sizes.code default).ell = (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell)
    (hrows : ∀ R : GroupRows,
      segmentGroupRows freshTable Sg none []
        (lotOwn segs p (D w.x) (readers w) (hd.take (hd.length - 0)) (0 + 0))
        (Stretch.carried p.carries c.2.2) 0 true = .ok R →
      i < ((R.members.filter (·.kept)).map (·.shape)).length ∧
      ((R.members.filter (·.kept)).map (·.shape)).getD i {} =
        ((switchSent p.sizes p.others).getD (1 + i) default).shape ∧
      VerifiableInference.Desc.K2.Honest.keptNo R.members i = n ∧
      VerifiableInference.Desc.K2.Honest.shapeOf R.members n = shapeAt J.P n ∧
      ∃ Rn, R.rows[n]? = some Rn ∧ ∀ r j,
        r < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows →
        j < (p.sizes.codes.base.getD
          ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell →
        Rn.mainF r j = (K1.rowsLaid J own₀ cs (wit w) hd' n).mainF r j)
    (mask : Bool) (r j : Nat) (y : Cb.Gl.E)
    (hy : switchMsgOff ch D readers (lotClosingAt lay segs) p (1 + i) k w hd mask r j = some y) :
    K1.msgTxt ch wit J own₀ n k w hd' mask r j = some y := by
  have hK : K1.msgTxt ch wit J own₀ n k w hd' mask r j =
      some (K1.rowsMsg (shapeAt J.P n) (K1.rowsLaid J own₀ cs (wit w) hd' n) mask r j) := by
    unfold K1.msgTxt
    rw [hcut]
    rfl
  rw [hK, ← hy]
  unfold switchMsgOff at hy ⊢
  by_cases hb : padB p.sizes.codes ((switchSent p.sizes p.others).getD (1 + i) default).shape mask r
      j = true
  · rw [if_pos hb] at hy
    cases hy
  · rw [if_neg hb]
    cases mask with
    | true =>
      rw [msgTxt_mask_bare ch D readers (lotClosingAt lay segs) p k w hd hH hV hn hbare r j]
      show some ((K1.rowsR J.P J.ride _ cs n).mask r j) = some zeroG
      rw [rowsR_mask_bare J.P J.ride _ cs n hride (by rw [hs]; exact hbare) r j]
      rfl
    | false =>
      have hdeg : ((shapeAt J.P n).mainDeg == 3) = false := by rw [hs]; exact h3
      have hKm : K1.rowsMsg (shapeAt J.P n) (K1.rowsLaid J own₀ cs (wit w) hd' n) false r j =
          algebraMap Cb.Gl.F Cb.Gl.E ((K1.rowsLaid J own₀ cs (wit w) hd' n).mainF r j) := by
        show (K1.rowsLaid J own₀ cs (wit w) hd' n).main ((shapeAt J.P n).mainDeg == 3) r j = _
        rw [hdeg]
        rfl
      rw [hKm]
      by_cases hin : (decide
          (r < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows) &&
          decide (j < (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell)) = true
      · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hin
        obtain ⟨hr, hj⟩ := hin
        obtain ⟨Wl, hW, hL⟩ := msgTxt_copy_f ch D readers (lotClosingAt lay segs) p k w hd hH hV hw
          hi hn h3 hr hj (by rw [ha1]; exact Nat.one_ne_zero)
          (fun hq => hb ((padInMain_iff_padB _ _ none ha1 hm hpad r j hj).1 hq))
        obtain ⟨y0, R, kp, hy0, hR, hkp, Hk⟩ := kept_at_closing hW (A := []) (Sg := Sg) hA
        obtain rfl : (none, 0) = y0 := Except.ok.inj hy0
        obtain ⟨e1, e2, e3, e4, Rn, e5, e6⟩ := hrows R hR
        have E := Hk i r j (by rw [hkp]; exact e1) (by rw [hkp, e2]; exact hr)
          (by rw [hell]; exact hj)
        rw [e3, e4, hdeg, List.getD_eq_getElem?_getD, e5] at E
        rw [hL, E, ← e6 r j hr hj]
        rfl
      · have hin' := Bool.eq_false_of_not_eq_true hin
        rw [msgTxt_beyond ch D readers (lotClosingAt lay segs) p k w hd hH hV hn hin', h3]
        show some (algebraMap Cb.Gl.F Cb.Gl.E ((K1.rowsR J.P J.ride _ cs n).mainF r j)) = _
        rw [rowsR_main_beyond J.P J.ride _ cs n (by rw [hs, hc]; exact hin')]
        rfl

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.rowsR_mask_bare
#print axioms ProofFile.Honest.K2.Law.rowsR_main_beyond
#print axioms ProofFile.Honest.K2.Law.msgOff_copy_is_firsts
