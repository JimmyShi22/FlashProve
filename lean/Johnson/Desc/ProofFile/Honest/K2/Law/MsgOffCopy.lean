-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MsgOffCopy.lean: the kind "the code switch" (K2): WHEREVER A
KEPT COPY's TEXT OFF THE PAD ANSWERS, THE TEXT OFF THE PAD OF THE SENDER IN FRONT ANSWERS THE SAME:
at one run: p₀: the switch that leads into the last segment in front of p; n: the public number of
the kept member i in that segment's group: for every (mask, r, j) and y: if `switchMsgOff`
(Honest/K2/MsgOff.lean) at p's message 1 + i answers y, so does it at p₀'s message n. AT EVERY
PLACE, not in range alone. Over the base field; where the two messages have one shape, with no mask
row and one answer, and the two places one list of codes. One statement with its proof: a split in
four; no definition.

  `msgOff_copy_is_senders`   THE END

The four: AT THE PAD the copy's text answers nothing · A MASK ENTRY: zero at both:
`msgTxt_mask_bare` (Honest/K2/Law/TxtBeyond.lean) · A MAIN ENTRY BEYOND THE RANGES: one value at
both: `msgTxt_beyond` (there) · A MAIN ENTRY IN RANGE, OFF THE PAD: `copy_txt_is_senders_f`
(Honest/K2/Law/CopyIsSendersF.lean), its premise on the pad's list had of the test by
`padInMain_iff_padB` (Honest/K2/Law/PadPlaces.lean).

Limits. ONE STEP BACK, NOT THE FIRST SENDER. ONE RUN: k, w and the two lists of challenges are
letters: a tie on a Script's message (`OwnMsgs`) runs over all of them: that step is not taken here.
ITS PREMISES ARE `copy_txt_is_senders_f`'s, less seven that are had here: the five on the place (hr,
hj, hp, hb', hj'), ha and h3₀; AND EIGHT PUBLIC ONES MORE: hs: the two messages have one shape · hc:
the two places have one list of codes · hbare, ha1, hm: no mask row, one answer, a main row · hpad:
the pad fits the row · hsk: the kept shape number i is the copy's · hell: the segment's code has the
copy's code's length. `copy_shape_ok` (Honest/K2/Law/KeptCopyShape.lean) gives hbare, ha1 and h3
where the public test on the places accepts; and that the copy's shape is entry i of `p.sizes.kept`:
hsk wants besides that this list is the list of S's group's kept shapes. Not called here. hs, hc,
hm, hpad, hell, and that equation of lists: shown nowhere by us. None of the premises on returns,
the book, the data and the challenges is paid here. What is WRITTEN where, at one run's coins. NO
LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyIsSendersF
import Johnson.Desc.ProofFile.Honest.K2.Law.TxtBeyond
import Johnson.Desc.ProofFile.Honest.K2.Law.PadPlaces
import Johnson.Desc.ProofFile.Honest.K2.MsgOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.K2.Honest (Left mainRows)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **WHEREVER THE COPY's TEXT OFF THE PAD ANSWERS, THE SENDER's ANSWERS THE SAME.** At one run; at
every place. One step back. -/
theorem msgOff_copy_is_senders (ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) {lay : OnBytes.Params.ReqLayout}
    {segs : List SegmentPub} (p₀ p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd₀ hd : List Fmt.Drawn)
    {c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries} (hH₀ : handed ch p₀ k = some c₀)
    {V₀ : Nat → Johnson.Prover.Send.Rows}
    (hV₀ : switchRowsLaid D readers (lotClosingAt lay segs) p₀ c₀ w hd₀ = .ok V₀)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : handed ch p k = some c)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt lay segs) p c w hd = .ok V)
    (hT : ∀ (i : Nat) (e₀ : Ahead),
      ((Bk.ahead.filter fun x => x.spender == ⟨p₀.place, 0⟩).filter (!·.once))[i]? = some e₀ →
      ∃ e, ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e ∧
        e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count)
    (hl : p₀.link ≤ p.link)
    (ho : ∀ i, i < (segs.take p₀.link).length →
      lotOwn segs p₀ (D w.x) (readers w) (hd₀.take (hd₀.length - 0)) (0 + i) =
        lotOwn segs p (D w.x) (readers w) (hd.take (hd.length - 0)) (0 + i))
    (hg : ∀ S ∈ segs.take p₀.link, challengesOr0 (hd₀.take (hd₀.length - 0)) S.gamma =
      challengesOr0 (hd.take (hd.length - 0)) S.gamma)
    {S : SegmentPub} (hS : (segs.take p.link).drop p₀.link = [S])
    (hSz : S.sizes = p₀.sizes) (hSent : S.sent.headD #[] = (switchSent p₀.sizes p₀.others))
    (hw : NoWord (switchSent p.sizes p.others)) {i : Nat} (hi : i < p.sizes.kept.length)
    (hn : 1 + i < (switchSent p.sizes p.others).size)
    (h3 : (((switchSent p.sizes p.others).getD (1 + i) default).shape.mainDeg == 3) = false)
    {n : Nat} (hnn : n = VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg S true) i)
    {kept : List OnBytes.OracleShape}
    (hk : kept = ((membersOfSeg S true).filter (·.kept)).map (·.shape))
    (ha' : i < kept.length)
    (hn₀ : n < (switchSent p₀.sizes p₀.others).size - 1)
    (hdeg : ((VerifiableInference.Desc.K2.Honest.shapeOf (membersOfSeg S true) n).mainDeg == 3) =
      (((switchSent p₀.sizes p₀.others).getD n default).shape.mainDeg == 3))
    (hdat : ∀ Wl : Left,
      mainRows p₀.sizes Wl (lotOwn segs p (D w.x) (readers w) (hd.take (hd.length - 0))
          (0 + (segs.take p₀.link).length)) n =
        mainRows p₀.sizes Wl (senderOwn (D w.x) (readers w) p₀) n)
    (e : Ahead)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[
      0 + ((segs.take p₀.link).map (·.messages)).sum + n]? = some e)
    (t1 : e.owner = ⟨p₀.place, 0⟩)
    (t2 : e.start = dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) n)
    (t3 : e.count = messageDue p₀.sizes.codes ((switchSent p₀.sizes p₀.others).getD n default).shape
      (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) n))
    (hs : ((switchSent p₀.sizes p₀.others).getD n default).shape =
      ((switchSent p.sizes p.others).getD (1 + i) default).shape)
    (hc : p₀.sizes.codes = p.sizes.codes)
    (hbare : ((switchSent p.sizes p.others).getD (1 + i) default).shape.maskRows = 0)
    (ha1 : ((switchSent p.sizes p.others).getD (1 + i) default).shape.answers = 1)
    (hm : 0 < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows)
    (hpad : (K1.stepsOf p.sizes.codes ((switchSent p.sizes p.others).getD (1 + i) default).shape
      none).pad ≤ (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell)
    (hsk : kept.getD i {} = ((switchSent p.sizes p.others).getD (1 + i) default).shape)
    (hell : (S.sizes.codes.base.getD S.sizes.code default).ell = (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell)
    (mask : Bool) (r j : Nat) (y : Cb.Gl.E)
    (hy : switchMsgOff ch D readers (lotClosingAt lay segs) p (1 + i) k w hd mask r j = some y) :
    switchMsgOff ch D readers (lotClosingAt lay segs) p₀ n k w hd₀ mask r j = some y := by
  have hn₀' : n < (switchSent p₀.sizes p₀.others).size := by omega
  unfold switchMsgOff at hy ⊢
  by_cases hb : padB p.sizes.codes ((switchSent p.sizes p.others).getD (1 + i) default).shape mask r
      j = true
  · rw [if_pos hb] at hy
    cases hy
  · rw [if_neg hb] at hy
    rw [hs, hc, if_neg hb, ← hy]
    cases mask with
    | true =>
      rw [msgTxt_mask_bare ch D readers (lotClosingAt lay segs) p₀ k w hd₀ hH₀ hV₀ hn₀'
          (by rw [hs]; exact hbare) r j,
        msgTxt_mask_bare ch D readers (lotClosingAt lay segs) p k w hd hH hV hn hbare r j]
    | false =>
      by_cases hin : (decide
          (r < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows) &&
          decide (j < (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell)) = true
      · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hin
        obtain ⟨hr, hj⟩ := hin
        exact (copy_txt_is_senders_f ch D readers p₀ p k w hd₀ hd hH₀ hV₀ hH hV hT hl ho hg hS hSz
          hSent hw hi hn h3 hr hj (by rw [ha1]; exact Nat.one_ne_zero)
          (fun hq => hb ((padInMain_iff_padB _ _ none ha1 hm hpad r j hj).1 hq)) hnn hk ha'
          (by rw [hsk]; exact hr) (by rw [hell]; exact hj) hn₀ hdeg (by rw [hs]; exact h3) hdat e
          he t1 t2 t3).symm
      · have hin' := Bool.eq_false_of_not_eq_true hin
        rw [msgTxt_beyond ch D readers (lotClosingAt lay segs) p₀ k w hd₀ hH₀ hV₀ hn₀'
            (by rw [hs, hc]; exact hin'),
          msgTxt_beyond ch D readers (lotClosingAt lay segs) p k w hd hH hV hn hin', hs]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.msgOff_copy_is_senders
