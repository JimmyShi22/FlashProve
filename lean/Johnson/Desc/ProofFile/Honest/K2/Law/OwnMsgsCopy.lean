-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OwnMsgsCopy.lean: the kind "the code switch" (K2): THE TIE ON
THE SCRIPT's MESSAGE AT A KEPT COPY FOLLOWS FROM THE TIE AT THE SENDER IN FRONT, AT ONE NUMBER IN
THE WITNESS: p₀: the switch that leads into the last segment in front of p; n: the public number of
the kept member i in that segment's group: if `OwnMsgs` (Honest/Thread/ScriptLots.lean, of other
authors) holds at the number num of p₀'s text off the pad at its message n, it holds at num of p's
text off the pad at its message 1 + i. One statement with its proof: three calls; no definition.

  `ownMsgs_copy_of_sender`   THE END

By: `msgTxt_inv` (Honest/K2/Law/MainTxt.lean): where the copy's text answers, p was handed its
stretches and laid its rows · `msgOff_copy_is_senders` (Honest/K2/Law/MsgOffCopy.lean): the sender's
text then answers the same · the sender's tie hm₀.

Limits. hm₀ IS A TIE TO A SCRIPT: a premise: no Script is laid. ONE LETTER num SERVES BOTH TIES. The
record at a switch (`K2SeatedL.msgs`, Honest/K2/SeatedL.lean) names at each message the number that
its table arr gives at the message's seat: THAT arr GIVES ONE NUMBER AT THE COPY's SEAT AND AT THE
SEAT OF p₀'s MESSAGE n IS NOT SAID HERE: a public equation on arr: whoever pays that field by this
law owes it. ONE STEP BACK: hm₀ stands at the switch in front: where its message n is itself a kept
copy, hm₀ wants this law once more. ITS OTHER PREMISES ARE `msgOff_copy_is_senders`'s. THOSE THAT
HANG ON NO RUN stand as there: public ones on the places, the segments and the shapes; the four
kinds on the book. THOSE THAT HANG ON THE RUN STAND IN ONE PREMISE, hrun, AT EVERY RUN THAT THE TIE
SPEAKS OF AND AT WHICH p LAYS ITS ROWS: that p₀ too is handed its stretches and lays its rows, at
what was heard up to fx₀; and the three agreements ho, hg, hdat between the two closings' data and
challenges. hrun IS SHOWN NOWHERE BY US. hNN: the sender's tie begins no later. Over the base field;
where the two messages have one shape with no mask row. It stands behind no step and no yes of a
verifier. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MsgOffCopy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (Left mainRows)
open ProofFile.Honest.FirstThread (Script OwnMsgs)

variable {W₀ Rc Xi Tr Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **THE TIE AT A KEPT COPY FOLLOWS FROM THE TIE AT THE SENDER IN FRONT**, at one number num in the
witness. One step back. -/
theorem ownMsgs_copy_of_sender (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N₀ N num fx₀ fx ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) {lay : OnBytes.Params.ReqLayout}
    {segs : List SegmentPub} (p₀ p : SwitchPlace) {i n : Nat}
    (hm₀ : OwnMsgs Q Vd N₀ num fx₀ (switchMsgOff ch D readers (lotClosingAt lay segs) p₀ n))
    (hNN : N₀ ≤ N)
    (hrun : ∀ (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn), Vd w → N ≤ hd.length →
      ∀ (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
        (V : Nat → Johnson.Prover.Send.Rows), handed ch p k = some c →
        switchRowsLaid D readers (lotClosingAt lay segs) p c w (hd.take fx) = .ok V →
        ∃ (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries)
          (V₀ : Nat → Johnson.Prover.Send.Rows), handed ch p₀ k = some c₀ ∧
          switchRowsLaid D readers (lotClosingAt lay segs) p₀ c₀ w (hd.take fx₀) = .ok V₀ ∧
          (∀ a, a < (segs.take p₀.link).length →
            lotOwn segs p₀ (D w.x) (readers w) ((hd.take fx₀).take ((hd.take fx₀).length - 0))
                (0 + a) =
              lotOwn segs p (D w.x) (readers w) ((hd.take fx).take ((hd.take fx).length - 0))
                (0 + a)) ∧
          (∀ S ∈ segs.take p₀.link,
            challengesOr0 ((hd.take fx₀).take ((hd.take fx₀).length - 0)) S.gamma =
              challengesOr0 ((hd.take fx).take ((hd.take fx).length - 0)) S.gamma) ∧
          ∀ Wl : Left,
            mainRows p₀.sizes Wl (lotOwn segs p (D w.x) (readers w)
                ((hd.take fx).take ((hd.take fx).length - 0))
                (0 + (segs.take p₀.link).length)) n =
              mainRows p₀.sizes Wl (senderOwn (D w.x) (readers w) p₀) n)
    (hT : ∀ (a : Nat) (e₀ : Ahead),
      ((Bk.ahead.filter fun x => x.spender == ⟨p₀.place, 0⟩).filter (!·.once))[a]? = some e₀ →
      ∃ e, ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[a]? = some e ∧
        e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count)
    (hl : p₀.link ≤ p.link)
    {S : SegmentPub} (hS : (segs.take p.link).drop p₀.link = [S])
    (hSz : S.sizes = p₀.sizes) (hSent : S.sent.headD #[] = (switchSent p₀.sizes p₀.others))
    (hw : NoWord (switchSent p.sizes p.others)) (hi : i < p.sizes.kept.length)
    (hn : 1 + i < (switchSent p.sizes p.others).size)
    (h3 : (((switchSent p.sizes p.others).getD (1 + i) default).shape.mainDeg == 3) = false)
    (hnn : n = VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg S true) i)
    {kept : List OnBytes.OracleShape}
    (hk : kept = ((membersOfSeg S true).filter (·.kept)).map (·.shape))
    (ha' : i < kept.length)
    (hn₀ : n < (switchSent p₀.sizes p₀.others).size - 1)
    (hdeg : ((VerifiableInference.Desc.K2.Honest.shapeOf (membersOfSeg S true) n).mainDeg == 3) =
      (((switchSent p₀.sizes p₀.others).getD n default).shape.mainDeg == 3))
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
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell) :
    OwnMsgs Q Vd N num fx (switchMsgOff ch D readers (lotClosingAt lay segs) p (1 + i)) := by
  intro k w hd hv hN mask r j y hy
  have hy' : switchMsgTxt ch D readers (lotClosingAt lay segs) p (1 + i) k w (hd.take fx) mask r j =
      some y := by
    unfold switchMsgOff at hy
    by_cases hb : padB p.sizes.codes
        ((switchSent p.sizes p.others).getD (1 + i) default).shape mask r j = true
    · rw [if_pos hb] at hy
      cases hy
    · rw [if_neg hb] at hy
      exact hy
  obtain ⟨c, V, hH, hV⟩ := msgTxt_inv hy'
  obtain ⟨c₀, V₀, hH₀, hV₀, ho, hg, hdat⟩ := hrun k w hd hv hN c V hH hV
  exact hm₀ k w hd hv (Nat.le_trans hNN hN) mask r j y
    (msgOff_copy_is_senders ch D readers p₀ p k w (hd.take fx₀) (hd.take fx) hH₀ hV₀ hH hV hT hl ho
      hg hS hSz hSent hw hi hn h3 hnn hk ha' hn₀ hdeg hdat e he t1 t2 t3 hs hc hbare ha1 hm hpad hsk
      hell mask r j y hy)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.ownMsgs_copy_of_sender
