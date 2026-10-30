-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KeptIsSenders.lean: the kind "the code switch" (K2): THE
CLOSING's KEPT MEMBER IS THE ROW OF THE SENDER IN FRONT: p₀: the switch that leads into the last
segment in front of the switch p. Where both closings return, the main entries of the kept member
number a of what p's closing returns are, in range, those of the row V n that p₀ itself laid, n the
kept member's number in the segment's group: AS FAR AS n IS A MESSAGE OF p₀'s OWN SENDING in front
of its last. Two statements with their proofs: joins; no definition.

  `walk_in_front_same`  the later walk over the segments in front of the sender returns what the
                        sender's own walk returned
  `kept_is_senders`     THE END

By: `kept_at_closing` (Honest/K2/Law/KeptAtClosing.lean): the kept member against the rows R that
p's closing laid anew · `copy_at_segment` (Honest/K2/Law/CopyAtSegment.lean): R.rows[n]? = some (V
n), at any R that `segmentGroupRows` returns at the sender's own fold · `closingFrom_passes`
(Honest/K2/Law/ClosingPasses.lean), taken at the sender's own link, `givesAll_carried`
(Honest/K2/Law/CarriedSame.lean), `lotClosingAt_inv`, `closingFrom_next`
(Honest/K2/Law/CopyAtClosing.lean): that the fold handed into that segment is the sender's W₀, and
that its first stretch's number is the count of all messages of the segments in front.

Limits. A THIRD LINK OF A LONGER CHAIN, behind CopyTxt.lean and KeptAtClosing.lean. ONE STEP BACK,
NOT THE FIRST SENDER: the message number n of p₀'s sending may itself be a kept copy: then V n is
again a copy's row. NOT the members that a sender of another kind sent later in the segment: hn
shuts them out. ITS PREMISES ARE `copy_at_closing`'s, with the list behind the segment empty:
RETURNS: both switches are handed their stretches; both closings return; the sender's laying returns
V · ON THE BOOK: hT; and at the message n an entry e with its owner, start and count · ON THE DATA
AND THE CHALLENGES: ho, hg; and at n: hd. None is paid here. THAT n IS THE NUMBER OF THE MESSAGE
WHOSE COPY p SENDS AS ITS MESSAGE 1 + a, AND THAT THE TWO HAVE ONE SHAPE, IS NOT SAID HERE: the flag
on the field is read off R's members. ROWS AGAINST A TABLE: not the texts. In range alone. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.KeptAtClosing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows)

variable {Bk : ProverCoinCounts}

/-- **The later walk over the segments in front of the sender returns what the sender's own walk
returned.** `closingFrom_passes` at l := l₀: nothing is left to walk. -/
theorem walk_in_front_same (table : FreshTable) {own₀ own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard₀ heard : List Fmt.Drawn} {k₀ k : Nat → Except String Stretch} (hk : GivesAll k₀ k)
    (segs : List SegmentPub) (l₀ : Nat)
    (ho : ∀ i, i < (segs.take l₀).length → own₀ (0 + i) = own (0 + i))
    (hg : ∀ S ∈ segs.take l₀, challengesOr0 heard₀ S.gamma = challengesOr0 heard S.gamma)
    {x₀ : Option (Left × List OnBytes.OracleShape) × Nat}
    (h₀ : closingFrom table own₀ heard₀ k₀ (segs.take l₀) 0 0 none = .ok x₀) :
    closingFrom table own heard k (segs.take l₀) 0 0 none = .ok x₀ := by
  rw [closingFrom_passes table hk segs (Nat.le_refl l₀) ho hg h₀,
    List.drop_eq_nil_of_le (List.length_take_le _ _)]
  rfl

/-- **THE CLOSING's KEPT MEMBER IS THE ROW OF THE SENDER IN FRONT.** V: the rows that p₀ laid. R:
the rows that p's closing laid anew of the segment S into which p₀ leads. One step back. -/
theorem kept_is_senders (ch : Nat) (p₀ p : SwitchPlace) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    (hT : ∀ (i : Nat) (e₀ : Ahead),
      ((Bk.ahead.filter fun x => x.spender == ⟨p₀.place, 0⟩).filter (!·.once))[i]? = some e₀ →
      ∃ e, ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e ∧
        e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count)
    {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {D : RowData} {Rd : Readers}
    {heard₀ heard : List Fmt.Drawn} {W₀ W : Left}
    (hW₀ : lotClosingAt lay segs p₀ D Rd heard₀ (Stretch.carried p₀.carries c₀.2.2) = .ok W₀)
    (hW : lotClosingAt lay segs p D Rd heard (Stretch.carried p.carries c.2.2) = .ok W)
    (hl : p₀.link ≤ p.link)
    (ho : ∀ i, i < (segs.take p₀.link).length →
      lotOwn segs p₀ D Rd heard₀ (0 + i) = lotOwn segs p D Rd heard (0 + i))
    (hg : ∀ S ∈ segs.take p₀.link, challengesOr0 heard₀ S.gamma = challengesOr0 heard S.gamma)
    {S : SegmentPub} (hS : (segs.take p.link).drop p₀.link = [S])
    (hSz : S.sizes = p₀.sizes) (hSent : S.sent.headD #[] = (switchSent p₀.sizes p₀.others))
    {own₀ : Nat → Nat → Nat → Cb.Gl.E} {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll freshTable p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) (mainRows p₀.sizes W₀ own₀) c₀.1 = .ok V) :
    ∃ (R : GroupRows) (prevKept kept : List OnBytes.OracleShape),
      segmentGroupRows freshTable S (some W₀) prevKept
        (lotOwn segs p D Rd heard (0 + (segs.take p₀.link).length))
        (Stretch.carried p.carries c.2.2) (0 + ((segs.take p₀.link).map (·.messages)).sum) true =
          .ok R ∧
      kept = (R.members.filter (·.kept)).map (·.shape) ∧
      ∀ a b j, a < kept.length → b < (kept.getD a {}).mainRows →
        j < (S.sizes.codes.base.getD S.sizes.code default).ell →
        VerifiableInference.Desc.K2.Honest.keptNo R.members a <
          (switchSent p₀.sizes p₀.others).size - 1 →
        mainRows p₀.sizes W₀ (lotOwn segs p D Rd heard (0 + (segs.take p₀.link).length))
            (VerifiableInference.Desc.K2.Honest.keptNo R.members a) =
          mainRows p₀.sizes W₀ own₀ (VerifiableInference.Desc.K2.Honest.keptNo R.members a) →
        ∀ e : Ahead,
          ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[
            0 + ((segs.take p₀.link).map (·.messages)).sum +
              VerifiableInference.Desc.K2.Honest.keptNo R.members a]? = some e →
          e.owner = ⟨p₀.place, 0⟩ →
          e.start = dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
            (switchFresh p₀.sizes p₀.others p₀.foldVars)
            (VerifiableInference.Desc.K2.Honest.keptNo R.members a) →
          e.count = messageDue p₀.sizes.codes ((switchSent p₀.sizes p₀.others).getD
              (VerifiableInference.Desc.K2.Honest.keptNo R.members a) default).shape
            (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars)
              (VerifiableInference.Desc.K2.Honest.keptNo R.members a)) →
          (W.kept a).main b j =
            (V (VerifiableInference.Desc.K2.Honest.keptNo R.members a)).main
              ((VerifiableInference.Desc.K2.Honest.shapeOf R.members
                (VerifiableInference.Desc.K2.Honest.keptNo R.members a)).mainDeg == 3) b j := by
  have hA : segs.take p.link = segs.take p₀.link ++ [S] := by
    have e := List.take_append_drop p₀.link (segs.take p.link)
    rw [hS, List.take_take, Nat.min_eq_left hl] at e
    exact e.symm
  obtain ⟨y, R, kept, hy, hR, hk, hmain⟩ := kept_at_closing hW hA
  obtain ⟨x₀, kp, hx₀, e₀⟩ := lotClosingAt_inv hW₀
  have hy' : closingFrom freshTable (lotOwn segs p D Rd heard) heard
      (Stretch.carried p.carries c.2.2) (segs.take p₀.link) 0 0 none = .ok x₀ :=
    walk_in_front_same freshTable (givesAll_carried ch p₀ p k c₀ h₀ c h hT) segs p₀.link ho hg hx₀
  obtain rfl : y = x₀ := Except.ok.inj (hy.symm.trans hy')
  have eb := closingFrom_next freshTable _ heard₀ _ (segs.take p₀.link) 0 0 none y hx₀
  rw [e₀, eb] at hR
  refine ⟨R, kp, kept, hR, hk, fun a b j ha hb hj hn hd e he t1 t2 t3 => ?_⟩
  have hr := copy_at_segment ch p₀ p k c₀ h₀ c h hR hSz hSent hV hn hd e he t1 t2 t3
  rw [hmain a b j ha hb hj, List.getD_eq_getElem?_getD, hr]
  rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.walk_in_front_same
#print axioms ProofFile.Honest.K2.Law.kept_is_senders
