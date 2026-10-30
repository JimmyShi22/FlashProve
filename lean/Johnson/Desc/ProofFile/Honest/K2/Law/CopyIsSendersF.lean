-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyIsSendersF.lean: the kind "the code switch" (K2): THE
SISTER OF `copy_txt_is_senders_e` (Honest/K2/Law/CopyIsSenders.lean) OVER THE BASE FIELD: off the
copy's pad, a main entry of the lot's text at p's kept copy number i is the entry at the same place
of message n of the switch p₀ in front. One statement with its proof; no definition.

  `copy_txt_is_senders_f`   THE END

By: the sister's own steps, with `msgTxt_copy_f` (Honest/K2/Law/CopyTxt.lean) in `msgTxt_copy_e`'s
stead. ONE STEP MORE: the copy's text is the first coordinate of the closing's kept entry, laid back
into the extension field; that entry is itself a base-field element of p₀'s row laid into the
extension field (`Rows.main` at the flag false): so the two are one.

Limits. ALL OF THE SISTER's, but for the field: h3 says that the copy lies over the base field; h3₀,
A PREMISE MORE, that p₀'s message n does: public; nothing here makes the two shapes equal. ONE STEP
BACK, NOT THE FIRST SENDER. OFF THE COPY's PAD: of the pad of p₀'s message nothing is asked. None of
the premises is paid here. An equation at one run's coins: what is WRITTEN where. NO LOT IS LAID.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyIsSenders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **The same over the base field.** h3₀: p₀'s message n lies over the base field too. -/
theorem copy_txt_is_senders_f (ch : Nat) (D : RowDataOf Xi)
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
    (hn : 1 + i < (switchSent p.sizes p.others).size) {r j : Nat}
    (h3 : (((switchSent p.sizes p.others).getD (1 + i) default).shape.mainDeg == 3) = false)
    (hr : r < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows)
    (hj : j < (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell)
    (ha : ((switchSent p.sizes p.others).getD (1 + i) default).shape.answers ≠ 0)
    (hp : (r, j) ∉ padInMain (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell
      ((switchSent p.sizes p.others).getD (1 + i) default).shape)
    {n : Nat} (hnn : n = VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg S true) i)
    {kept : List OnBytes.OracleShape}
    (hk : kept = ((membersOfSeg S true).filter (·.kept)).map (·.shape))
    (ha' : i < kept.length) (hb' : r < (kept.getD i {}).mainRows)
    (hj' : j < (S.sizes.codes.base.getD S.sizes.code default).ell)
    (hn₀ : n < (switchSent p₀.sizes p₀.others).size - 1)
    (hdeg : ((VerifiableInference.Desc.K2.Honest.shapeOf (membersOfSeg S true) n).mainDeg == 3) =
      (((switchSent p₀.sizes p₀.others).getD n default).shape.mainDeg == 3))
    (h3₀ : (((switchSent p₀.sizes p₀.others).getD n default).shape.mainDeg == 3) = false)
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
      (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) n)) :
    switchMsgTxt ch D readers (lotClosingAt lay segs) p (1 + i) k w hd false r j =
      switchMsgTxt ch D readers (lotClosingAt lay segs) p₀ n k w hd₀ false r j := by
  obtain ⟨Wl, hW, hL⟩ := msgTxt_copy_f ch D readers (lotClosingAt lay segs) p k w hd hH hV hw hi hn
    h3 hr hj ha hp
  obtain ⟨Wl₀, hW₀, hR₀⟩ := rowsLaid_inv hV₀
  obtain ⟨R, pk, kp, hR, hkp, H⟩ := kept_is_senders ch p₀ p k c₀ hH₀ c hH hT hW₀ hW hl ho hg hS hSz
    hSent hR₀
  have hM : R.members = membersOfSeg S true := segmentRows_members hR
  have hkk : kp = kept := by rw [hkp, hM, hk]
  have H' := H i r j
  rw [hM, ← hnn, hkk] at H'
  have E := H' ha' hb' hj' hn₀ (hdat Wl₀) e he t1 t2 t3
  rw [hL, E, msgTxt_rows ch D readers (lotClosingAt lay segs) p₀ n k w hd₀ hH₀ hV₀ false r j, hdeg]
  show some (algebraMap Cb.Gl.F Cb.Gl.E ((V₀ n).main
      (((switchSent p₀.sizes p₀.others).getD n default).shape.mainDeg == 3) r j).c0) =
    some ((V₀ n).main (((switchSent p₀.sizes p₀.others).getD n default).shape.mainDeg == 3) r j)
  rw [h3₀]
  show some (algebraMap Cb.Gl.F Cb.Gl.E (algebraMap Cb.Gl.F Cb.Gl.E ((V₀ n).mainF r j)).c0) =
    some (algebraMap Cb.Gl.F Cb.Gl.E ((V₀ n).mainF r j))
  rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.copy_txt_is_senders_f
