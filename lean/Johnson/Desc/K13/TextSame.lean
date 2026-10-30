-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/TextSame.lean (kind K13): THEOREMS: Johnson/Desc/K13/Text.lean's four functions,
which call the kind's own text (Johnson/Desc/K13/Own.lean) and, for the test on the public
shape, Johnson/Desc/Own/Lin.lean's linFits, return at all arguments what the same bodies return with
six functions of the program `verify-on-bytes` in their place: each is shown equal to that
body, written out. So a law that is proved of those bodies carries over by rewriting. One more
for Johnson/Desc/K13/PscStep.lean's `pscP`.

-/
import Johnson.Desc.K13.Text
import Johnson.Desc.K13.OwnLaws
import Johnson.Desc.Own.LinAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13
open OnBytes OnBytes.Params
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.Ground (takeMasksP newGroupP joinP addRowsP)

theorem front_same (st : Statement) (S : LinShape) (indexMasks : Nat) (pile : List TensorRow)
    (due : Bool) (heard : Option E) (n : Nat) :
    front st S indexMasks pile due heard n = (do
      need "K13.reply-heard" (!due || heard.isSome)
      need "K13.pile-count" (pile.length == n)
      need "K13.pile-on-the-table" (memberRowsFit st S indexMasks pile)) := by
  unfold front
  rw [Own.pileOnTable_agrees]

theorem batt_same (owed : RowsOwed) (kCol n : Nat) (pile : List TensorRow) (ledger : Nat) (d : St)
    (rs : List Fmt.RoundView) :
    batt owed kCol n pile ledger d rs = (do
      need "K13.nothing-owed" owed.isNone
      need "K13.pile-form" (Batt.fits kCol pile)
      match rs with
      | [] => .error "K13.sigma-round"
      | r :: rs' =>
        let x ← oneDrawn "K13.sigma-one-drawn" r
        need "K13.rows-counted" (pile.length == n)
        let t ← there "K13.mask-entries" (takeMasksP d ledger (Batt.masksOf kCol))
        let h ← heard rs'
        let o ← there "K13.sumcheck-sizes"
          (Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) (t.1.map fun i => ⟨ledger, i⟩) h)
        need "K13.a-coefficient-a-row" (o.rowMaps.length == pile.length)
        pure (Batt.rowOf pile o, t.2)) := by
  unfold batt
  simp only [Own.pileForm_agrees, Own.runSum_agrees]
  cases rs <;> rfl

theorem quiet_same (codes : Codes) (S : LinShape) :
    quiet codes S = (do
      need "K13.shape-lawful" (linOk codes S)
      there "K13.message-W" (linMessageW S)) := by
  unfold quiet
  rw [Own.messageW_agrees, VerifiableInference.Desc.Own.linFits_eq]

theorem rows_same (S : LinShape) (claim : LinClaim) (ids : Array Nat) (d : St) :
    rows S claim ids d = (do
      let w ← there "K13.W-sent" ids[0]?
      let b ← there "K13.own-group" (newGroupP d S.w.code S.ownMaskCode)
      let d₁ ← joinAll b.1 (listOfT (claim.masks.toList.map (·.oracle))) b.2
      let d₂ ← there "K13.join-W" (joinP d₁ b.1 w false)
      let split ← there "K13.split-sent" (if S.ownSplitNeeded then ids[1]? else some noId)
      let d₃ ← there "K13.join-split"
        (if S.ownSplitNeeded then joinP d₂ b.1 split false else some d₂)
      let mask ← there "K13.mask-sent" (if S.masksAhead then ids.back?.map some else some none)
      let row ← there "K13.eval-row" (linEvalRow S claim w (linLayW d₃.st.codes S))
      let d₄ ← there "K13.eval-laid" (addRowsP d₃ b.1 [row])
      pure ({ w := w, split := split, own := b.1, mask := mask, claim := claim }, d₄)) := by
  unfold rows
  simp only [Own.evalRow_agrees]
  rfl

theorem pscP_same (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (es : List Fmt.Entry)
    (rs : List Fmt.RoundView) :
    First.End.pscP c S fresh es rs =
      (First.End.hearP (Psc.sizeOf c S) es rs).bind (Psc.run c S fresh) := by
  unfold First.End.pscP
  simp only [Own.runSum_agrees]

end VerifiableInference.Desc.K13
