-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Term/OwnersTextsCoverTheMaskRow.lean: the honest side of the kind
"lookup" (K3): the whole-message texts of the two kinds that send a link's mask row, the shared
sending (K1) and the code switch (K2), cover the lookups' text `maskRowEntriesText`
(Honest/K3/Term/MaskRowFromScript.lean), in the sense of `Covers` (Honest/Small/Covers.lean).

Why. The lookups' named premise `ScriptLaysOwnersCoinsInMaskRow` is `OwnMsgs` at a text of ours, which
stands in nobody's list of lots. By `ownMsgs_of_covers` it follows, at every Script, from `OwnMsgs` at
the owner's own text, once that text covers ours. The two laws here say that it does: general in the
job (K1) and in the place (K2); no size, no head, no Script.

  `maskRowEntriesTextAnswered`          what an answer of our text says
  `cutHoldsOwnersCoin`                  a coin of a cut from 0 on is the coin of that number
  `sendingCoversMaskRowEntries`         K1: the text `K1.msgTxt` of a message whose table does not ride
  `switchCoversMaskRowEntries`          K2: the text `K2.switchMsgTxt` of a message that is not the last
  `scriptLaysOwnersCoinsOfSending`      the named premise from `OwnMsgs` at K1's text
  `scriptLaysOwnersCoinsOfSwitch`       the named premise from `OwnMsgs` at K2's text

Joins, over the owners' own laws: K1: `msgTxt_mask_slot` (Honest/K1/ScriptMaskSlot.lean), `mask_in`,
`ce_eq` (Honest/K1/MaskLaw.lean), `cut_of_count` (Honest/K1/SeatedLaw.lean). K2: `msgTxt_answers`
(Honest/K2/Law/LotsAnswer.lean), `msgTxt_mask`, `msgTxt_mask_in`, `own_of_handed`
(Honest/K2/Law/MaskTxt.lean). The frame's: `cut_coinsE` (Honest/Law/Rule/Spent.lean), `val_coin`
(Honest/Law/Rule/CoinBack.lean).

Limits. Start and owner are the SENDER's own letters (`K1.maskStart`, `K2.maskBase`, the part
number 0 at the sender's place): that these are the owner and the start that the book's maker finds
(`ownerOf`), which message of the sending holds a link's mask row, and what its number in the witness
is, is not said here. One mask row alone. The premises are shown here at no job, place, book or
input: K1's hHasCoins; K2's hClosing, hHanded, hServes, hRoomy, hFits and hPublic (which reads the
input's public instance). `Covers` may hold emptily: where our text answers nowhere it says nothing.
`OwnMsgs` at the owner's text is a premise of the last two. Nothing is claimed on soundness,
completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.MaskRowFromScript
import Johnson.Desc.ProofFile.Honest.K1.ScriptMaskSlot
import Johnson.Desc.ProofFile.Honest.K1.SeatedLaw
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswer
import Johnson.Desc.ProofFile.Honest.Law.Rule.Spent
import Johnson.Desc.ProofFile.Honest.Law.Rule.CoinBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open OnBytes.Slice (GE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs MsgLot Covers ownMsgs_of_covers)

/-! ## 1 Two tools -/

/-- What an answer of the text says: a mask row, number 0, a place below count, and the owner has
the coin. -/
theorem maskRowEntriesTextAnswered {Bk : ProverCoinCounts} {W : Type} {owner : Addr} {start count : Nat}
    {k : Coins Bk} {w : W} {hd : List Fmt.Drawn} {mask : Bool} {row place : Nat} {y : GE}
    (hAnswer : maskRowEntriesText Bk owner start count k w hd mask row place = some y) :
    mask = true ∧ row = 0 ∧ place < count ∧
      ((coinsE (k.look 0 owner).2)[start + place]?).map Reading.gl.val = some y := by
  unfold maskRowEntriesText at hAnswer
  by_cases c : mask = true ∧ row = 0 ∧ place < count
  · rw [if_pos c] at hAnswer
    exact ⟨c.1, c.2.1, c.2.2, hAnswer⟩
  · rw [if_neg c] at hAnswer
    cases hAnswer

/-- A coin of a cut that begins at the first coin is the coin of the same number. -/
theorem cutHoldsOwnersCoin {whole part : Due} {coins : Cs whole} {cut : Cs part}
    (hCut : coins.cut ⟨0, 0⟩ part = some cut) {number : Nat} (hNumber : number < part.e) {y : GE}
    (hCoin : ((coinsE coins)[number]?).map Reading.gl.val = some y) :
    cut.e ⟨number, hNumber⟩ = y := by
  have e : (coinsE cut)[number]? = (coinsE coins)[number]? := by
    rw [cut_coinsE hCut, List.getElem?_take_of_lt hNumber]
    rfl
  have e' : (coinsE cut)[number]? =
      some (OnBytes.E.ofTriple (OnBytes.Slice.ofE (cut.e ⟨number, hNumber⟩))) := by
    unfold coinsE
    rw [List.getElem?_ofFn, dif_pos hNumber]
  rw [← e, e'] at hCoin
  exact (val_coin _).symm.trans (Option.some.inj hCoin)

/-! ## 2 The shared sending (K1) -/

/-- **K1's WHOLE-MESSAGE TEXT COVERS THE LOOKUPS' TEXT**, general in the job J. n: the message's
number in the sending. CONDITIONAL on: hMessage; hNoRide, no table rides at that message;
hOneMaskRow; hCount, count is at most the mask code's message length; hHasCoins, the book's count at
the sending part is the part's own. -/
theorem sendingCoversMaskRowEntries {Bk : ProverCoinCounts} {W Wl X : Type} (wit : Wl → W)
    (J : K1.SendJob W X) (own₀ : X) (n messageNumber challengesRead count : Nat)
    (valid : Wl → Prop) (challengesInFront : Nat) (hMessage : n < J.P.sent.size)
    (hNoRide : J.ride n = none) (hOneMaskRow : (shapeAt J.P n).maskRows = 1)
    (hCount : count ≤ (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell)
    (hHasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = K1.dueR J.P J.ride) :
    Covers valid challengesInFront
      (⟨messageNumber, challengesRead, K1.msgTxt 0 wit J own₀ n⟩ : MsgLot Bk Wl)
      ⟨messageNumber, 0,
        maskRowEntriesText Bk ⟨J.P.place, 0⟩ (K1.maskStart J.P J.ride n) count⟩ := by
  refine ⟨rfl, fun k w hd _ _ mask row place y q => ?_⟩
  obtain ⟨rfl, rfl, hp, q'⟩ := maskRowEntriesTextAnswered (w := w) (hd := hd.take 0) q
  have hν : place < (shapeAt J.P n).maskRows *
      (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell := by
    rw [hOneMaskRow, Nat.one_mul]
    exact Nat.lt_of_lt_of_le hp hCount
  have e := K1.msgTxt_mask_slot 0 wit J own₀ n place k w (hd.take challengesRead) hNoRide hν
  rw [hOneMaskRow, Nat.mod_one, Nat.div_one] at e
  obtain ⟨c, hc⟩ := K1.cut_of_count (Nat.zero_le 1) hHasCoins k
  show K1.msgTxt 0 wit J own₀ n k w (hd.take challengesRead) true 0 place = some y
  rw [e, hc]
  show some (K1.ce c (K1.maskStart J.P J.ride n + place)) = some y
  rw [K1.ce_eq _ c _ (K1.mask_in J.P J.ride n place hMessage hNoRide hν)]
  exact congrArg some (cutHoldsOwnersCoin hc _ q')

/-- **The named premise from `OwnMsgs` at K1's text**, at every Script. CONDITIONAL on the same and on
hOwn. -/
theorem scriptLaysOwnersCoinsOfSending {Bk : ProverCoinCounts} {W Wl X Cells Tok : Type}
    {Q : Script Bk Wl Cells Tok MsgT} (wit : Wl → W) (J : K1.SendJob W X) (own₀ : X)
    (n messageNumber challengesRead count : Nat) (valid : Wl → Prop) (challengesInFront : Nat)
    (hMessage : n < J.P.sent.size) (hNoRide : J.ride n = none)
    (hOneMaskRow : (shapeAt J.P n).maskRows = 1)
    (hCount : count ≤ (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell)
    (hHasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = K1.dueR J.P J.ride)
    (hOwn : OwnMsgs Q valid challengesInFront messageNumber challengesRead
      (K1.msgTxt 0 wit J own₀ n)) :
    ScriptLaysOwnersCoinsInMaskRow Q valid challengesInFront messageNumber ⟨J.P.place, 0⟩
      (K1.maskStart J.P J.ride n) count :=
  ownMsgs_of_covers (sendingCoversMaskRowEntries wit J own₀ n messageNumber challengesRead count
    valid challengesInFront hMessage hNoRide hOneMaskRow hCount hHasCoins) hOwn

/-! ## 3 The code switch (K2) -/

/-- **K2's WHOLE-MESSAGE TEXT COVERS THE LOOKUPS' TEXT**, general in the place p, at the closing as
the kind's lot lays it. n: the message's number in the switch's sending. CONDITIONAL on: hMessage;
hNotLast, it is not the next fold's mask; hOneMaskRow; hCount; and what K2's authors name as the
conditions under which the text answers: hClosing, hHanded, hServes, hRoomy, hFits, and hPublic at
every valid input's public instance. -/
theorem switchCoversMaskRowEntries {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type} (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) (p : K2.SwitchPlace)
    (n messageNumber challengesRead count : Nat) (valid : Local W₀ Rc Xi Tr → Prop)
    (challengesInFront : Nat) (hMessage : n < (K2.switchSent p.sizes p.others).size)
    (hNotLast : n ≠ (K2.switchSent p.sizes p.others).size - 1)
    (hOneMaskRow : ((K2.switchSent p.sizes p.others).getD n default).shape.maskRows = 1)
    (hCount : count ≤ K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n)
    (hClosing : K2.closingOk K2.freshTable (segs.take p.link) p = true)
    (hHanded : ∀ k : Coins Bk, (K2.handed 0 p k).isSome = true)
    (hServes : p.sizes.serves = true) (hRoomy : p.sizes.roomy = true)
    (hFits : K2.placeFits p = true)
    (hPublic : ∀ w, valid w → K2.publicOk D lay p (segs.take p.link) w.x = true) :
    Covers valid challengesInFront
      (⟨messageNumber, challengesRead,
        K2.switchMsgTxt 0 D readers (K2.lotClosingAt lay segs) p n⟩ :
        MsgLot Bk (Local W₀ Rc Xi Tr))
      ⟨messageNumber, 0, maskRowEntriesText Bk ⟨p.place, 0⟩
        (K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
          (K2.switchFresh p.sizes p.others p.foldVars) n) count⟩ := by
  refine ⟨rfl, fun k w hd hv _ mask row place y q => ?_⟩
  obtain ⟨rfl, rfl, hp, q'⟩ := maskRowEntriesTextAnswered (w := w) (hd := hd.take 0) q
  have hν : place < K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n :=
    Nat.lt_of_lt_of_le hp hCount
  obtain ⟨y', hy'⟩ := K2.Law.msgTxt_answers 0 D readers lay segs p hClosing n k w
    (hd.take challengesRead) true 0 place (hHanded k) hServes hRoomy (hPublic w hv) hFits
  have e := K2.Law.msgTxt_mask 0 D readers (K2.lotClosingAt lay segs) p hMessage hNotLast hν k w
    (hd.take challengesRead) (by rw [hOneMaskRow, Nat.mod_one, Nat.div_one, hy']; rfl)
  rw [hOneMaskRow, Nat.mod_one, Nat.div_one] at e
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hHanded k)
  have hcut := K2.Law.own_of_handed 0 p k c hc
  have hin := K2.Law.msgTxt_mask_in p hFits hMessage hNotLast place hν
  show K2.switchMsgTxt 0 D readers (K2.lotClosingAt lay segs) p n k w (hd.take challengesRead)
    true 0 place = some y
  rw [e, hcut]
  show (c.1.eAt _).toOption = some y
  unfold Cs.eAt
  rw [dif_pos hin]
  exact congrArg some (cutHoldsOwnersCoin hcut hin q')

/-- **The named premise from `OwnMsgs` at K2's text**, at every Script. CONDITIONAL on the same and on
hOwn. -/
theorem scriptLaysOwnersCoinsOfSwitch {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Cells Tok : Type}
    {Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT} (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) (p : K2.SwitchPlace)
    (n messageNumber challengesRead count : Nat) (valid : Local W₀ Rc Xi Tr → Prop)
    (challengesInFront : Nat) (hMessage : n < (K2.switchSent p.sizes p.others).size)
    (hNotLast : n ≠ (K2.switchSent p.sizes p.others).size - 1)
    (hOneMaskRow : ((K2.switchSent p.sizes p.others).getD n default).shape.maskRows = 1)
    (hCount : count ≤ K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n)
    (hClosing : K2.closingOk K2.freshTable (segs.take p.link) p = true)
    (hHanded : ∀ k : Coins Bk, (K2.handed 0 p k).isSome = true)
    (hServes : p.sizes.serves = true) (hRoomy : p.sizes.roomy = true)
    (hFits : K2.placeFits p = true)
    (hPublic : ∀ w, valid w → K2.publicOk D lay p (segs.take p.link) w.x = true)
    (hOwn : OwnMsgs Q valid challengesInFront messageNumber challengesRead
      (K2.switchMsgTxt 0 D readers (K2.lotClosingAt lay segs) p n)) :
    ScriptLaysOwnersCoinsInMaskRow Q valid challengesInFront messageNumber ⟨p.place, 0⟩
      (K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) n) count :=
  ownMsgs_of_covers (switchCoversMaskRowEntries D readers lay segs p n messageNumber challengesRead
    count valid challengesInFront hMessage hNotLast hOneMaskRow hCount hClosing hHanded hServes
    hRoomy hFits hPublic) hOwn

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.maskRowEntriesTextAnswered
#print axioms ProofFile.Honest.K3.Term.cutHoldsOwnersCoin
#print axioms ProofFile.Honest.K3.Term.sendingCoversMaskRowEntries
#print axioms ProofFile.Honest.K3.Term.scriptLaysOwnersCoinsOfSending
#print axioms ProofFile.Honest.K3.Term.switchCoversMaskRowEntries
#print axioms ProofFile.Honest.K3.Term.scriptLaysOwnersCoinsOfSwitch
