-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/TextIs.lean: what four functions of kind K13's text are, written out: each
calls, under its tests' names, `verify-on-bytes`'s pure functions `memberRowsFit`, `Batt.fits`,
`Psc.run`, `linMessageW`, `linEvalRow` and `LinShape.ownSplitNeeded`. The laws of this folder unfold
the text through these four equations alone, so that they stand whether the text calls these
functions by name or has text of its own that agrees with them. Statements with their proofs.
Main names: `front_is`, `batt_is`, `quiet_is`, `rows_is`.
This form of the file stands over the text that has text of its own for them (K13/Own.lean): each
equation is a theorem of K13/TextSame.lean.

What is not claimed. Nothing beyond the four equations.

-/
import Johnson.Desc.K13.TextSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.Ground (takeMasksP newGroupP joinP addRowsP)

/-- The front. -/
theorem front_is (st : Statement) (S : LinShape) (indexMasks : Nat) (pile : List TensorRow)
    (due : Bool) (heard : Option E) (n : Nat) :
    front st S indexMasks pile due heard n = (do
      need "K13.reply-heard" (!due || heard.isSome)
      need "K13.pile-count" (pile.length == n)
      need "K13.pile-on-the-table" (memberRowsFit st S indexMasks pile)) :=
  K13.front_same st S indexMasks pile due heard n

/-- The batching. -/
theorem batt_is (owed : RowsOwed) (kCol n : Nat) (pile : List TensorRow) (ledger : Nat) (d : St)
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
        pure (Batt.rowOf pile o, t.2)) :=
  K13.batt_same owed kCol n pile ledger d rs

/-- The quiet part. -/
theorem quiet_is (codes : Codes) (S : LinShape) :
    quiet codes S = (do
      need "K13.shape-lawful" (linOk codes S)
      there "K13.message-W" (linMessageW S)) :=
  K13.quiet_same codes S

/-- Behind W's commitment. -/
theorem rows_is (S : LinShape) (claim : LinClaim) (ids : Array Nat) (d : St) :
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
      pure ({ w := w, split := split, own := b.1, mask := mask, claim := claim }, d₄)) :=
  K13.rows_same S claim ids d

end VerifiableInference.Desc.K13.Law
