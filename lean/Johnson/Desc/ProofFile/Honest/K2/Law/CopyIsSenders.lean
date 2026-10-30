-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyIsSenders.lean: the kind "the code switch" (K2): OFF THE
COPY's PAD, A KEPT COPY's TEXT IS THE TEXT OF THE SENDER IN FRONT: p₀: the switch that leads into
the last segment S in front of the switch p. A main entry of the lot's text `switchMsgTxt`
(Honest/K2/ScriptLots.lean) at p's kept copy number i (its message 1 + i), off the places of that
copy's own pad, is the entry at the same place of p₀'s message number n: n THE PUBLIC NUMBER of the
kept member i in S's group (`membersOfSeg`, Honest/K2/Law/GroupMembers.lean). Over the extension
field. One statement with its proof: a join; no definition.

  `copy_txt_is_senders_e`   THE END

By, each called once: `msgTxt_copy_e` (Honest/K2/Law/CopyTxt.lean): the copy's text is the closing's
kept member · `kept_is_senders` (Honest/K2/Law/KeptIsSenders.lean): that member is the sender's row
· `segmentRows_members` (GroupMembers.lean): the group's members are the public ones ·
`rowsLaid_inv` (Honest/K2/Law/SenderOwn.lean), `msgTxt_rows` (Honest/K2/Law/MainTxt.lean): the
sender's rows and its text.

Limits. ONE STEP BACK, NOT THE FIRST SENDER: p₀'s message n may itself be a kept copy; then the law
can be called again at p₀ and the switch in front of it, under its premises there. WHOSE PAD: the
premise hp reads `padInMain` at the shape of p's message 1 + i: the copy's. No premise reads it at
the shape of p₀'s message n, and no premise makes these two shapes equal: so (r, j) is not known to
lie off the pad of the message on the equation's right. AT THE COPY's PAD NOTHING IS SAID HERE. What
stands at a pad's place in the main rows is another file's: `msgTxt_pad_e`, `msgTxt_pad_f`
(Honest/K2/Law/PadTxt.lean, not called): at any message of a switch's sending: the coin at a public
number of that switch's own stretch: so of p's at the copy, of p₀'s at its message; that the two
coins part in value is said nowhere. NOT the members that a sender of another kind sent later in the
segment (hn₀). MAIN ROWS OVER THE EXTENSION FIELD ALONE (h3). ITS PREMISES, BY KIND. RETURNS: both
switches are handed their stretches; both lay their rows. PUBLIC, ON THE PLACES AND THE SEGMENTS:
hl, hS, hSz, hSent; hw, hi, hn, h3, hr, hj, ha, hp: `msgTxt_copy_e`'s · hnn, hk: n and the kept
shapes, pinned · ha', hb', hj', hn₀: the place lies in range at S too · hdeg: S's member n and p₀'s
message n agree on the field. THAT THE COPY's SHAPE IS THE MEMBER's IS NOT ASKED AND NOT SAID: the
ranges are asked at both. ON THE BOOK: hT; he, t1, t2, t3. ON THE DATA AND THE CHALLENGES: ho, hg,
hdat. None is paid here, nor are they shown to hold together. An equation at one run's coins: what
is WRITTEN where. NO LOT IS LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.KeptIsSenders
import Johnson.Desc.ProofFile.Honest.K2.Law.GroupMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **OFF THE COPY's PAD, A KEPT COPY's TEXT IS THE TEXT OF THE SENDER IN FRONT**, over the
extension field. i: the kept member's number. n: its number in the group of the segment S. One step
back. -/
theorem copy_txt_is_senders_e (ch : Nat) (D : RowDataOf Xi)
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
    (h3 : (((switchSent p.sizes p.others).getD (1 + i) default).shape.mainDeg == 3) = true)
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
  obtain ⟨Wl, hW, hL⟩ := msgTxt_copy_e ch D readers (lotClosingAt lay segs) p k w hd hH hV hw hi hn
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
  rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.copy_txt_is_senders_e
