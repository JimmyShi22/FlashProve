-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/LayersLinkCells.lean: a layers' link (fourteen members of the
chain) in the table of steps on shapes (TabL.cells, Johnson/AtFull/Shape/TabLetters.lean; a cell is
one member's step), by number. The cell of the layers' own rounds sets the invariant
OwnRecordHeard (LayersLightRows.lean); the four cells after it keep the component own; and a light
cell for the batching stands under the table's, one way, at the invariant. General in the letters L
(the record TabLetters) and in the link l (even, below 24): no link is named. Nothing is evaluated.

Why. LayersLightRows.lean needs its invariant at the batching's cell. This file sets it at the cell
of the layers' own rounds and shows, by number, that the four cells between keep the component on
which it depends.

  refusingCell_keepsOwn   a cell that returns an error keeps own.
  readsCell_keepsOwn, drawCell_keepsOwn, digitsCell_keepsOwn, lookupDigitsCell_keepsOwn   the four
                          cells (the reads' at an even link).
  runOverCells_keepsOwn   a run over cells that keep own keeps it.
  **layersLinkRun_keepsOwn**   the run over the members 14 l + 5 … 14 l + 8 keeps own.
  **ownRoundsCell_laysOwnHeard**   where the cell of the layers' own rounds returns y,
                          OwnRecordHeard L.XG.layers hp g y.1, hp the group's plan: under "the
                          letter k4own is the hearing on shapes at the parameters that the cell
                          sets".
  layersBatchingLight L l   the light step: batchGSL.1 (Johnson/AtFull/Shape/TabLight.lean) over
                          layersLightRows; where a number is lacking it returns an error.
  **layersBatchingLight_standsUnder**   at an even l below 24, at a shape with the invariant: where
                          layersBatchingLight returns y, the table's cell returns y.

Limits. One way. From returns alone. The premise of ownRoundsCell_laysOwnHeard on the letter is an
equation of functions; ownRoundsLetter_atNumerals (OwnRoundsStepClosedForm.lean) shows it at LWn X
where the group has a plan. No run over a whole link is joined here. What a cell costs is not said.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLightRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Desc.First.K4.Rt
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9 (testsWhere)
open IM (subAt)

/-- A cell that returns an error keeps own. -/
theorem refusingCell_keepsOwn (why : String) : WholeStepKeepsOwn (noCell why).1 := by
  intro x y e
  exact nomatch e

/-- The reads' cell at an even link keeps own. -/
theorem readsCell_keepsOwn (L : TabLetters) (l : Nat) (he : l % 2 =
    0) : WholeStepKeepsOwn (TabL.reads L l).1 := by
  unfold TabL.reads
  split
  · rw [if_pos (by simpa using he)]
    split
    · exact readsA_keepsOwn (readsGS_keepsOwn _ _ _ _) _
    · exact refusingCell_keepsOwn _
  · exact refusingCell_keepsOwn _

/-- The draw's cell keeps own. -/
theorem drawCell_keepsOwn (L : TabLetters) (l : Nat) : WholeStepKeepsOwn (TabL.draw L l).1 := by
  unfold TabL.draw
  split
  · exact wholeStepKeepsOwn_ofStep (drawStep_keepsOwn _)
  · exact refusingCell_keepsOwn _

/-- The digits' cell keeps own. -/
theorem digitsCell_keepsOwn (L : TabLetters) (l : Nat) : WholeStepKeepsOwn (TabL.digits L l).1 := by
  unfold TabL.digits
  split
  · exact digitsA_keepsOwn _ _ _
  · exact refusingCell_keepsOwn _

/-- The lookup's digits' cell keeps own. -/
theorem lookupDigitsCell_keepsOwn (L : TabLetters) (l : Nat) : WholeStepKeepsOwn (TabL.lookDigits L
    l).1 := by
  unfold TabL.lookDigits
  split
  · exact wholeStepKeepsOwn_ofStep (digitsG_keepsOwn _ _ _ _)
  · exact refusingCell_keepsOwn _

/-- A run over cells that keep own keeps it. -/
theorem runOverCells_keepsOwn (L : TabLetters) (m : Nat) : ∀ n : Nat,
    (∀ i, i < n → WholeStepKeepsOwn (TabL.cells L (m + i)).1) →
    ∀ x y : ShA, (shapeL L).runFrom m n x = .ok y → y.1.own = x.1.own
  | 0, _, x, y, h => by
    obtain rfl : x = y := Except.ok.inj h
    rfl
  | n + 1, hk, x, y, h => by
    have h' : ((shapeL L).runFrom m n x).bind (TabL.cells L (m + n)).1 = .ok y := h
    cases hr : (shapeL L).runFrom m n x with
    | error e =>
      rw [hr] at h'
      exact nomatch h'
    | ok z =>
      rw [hr] at h'
      exact (hk n (Nat.lt_succ_self n) z y h').trans
        (runOverCells_keepsOwn L m n (fun i hi => hk i (Nat.lt_succ_of_lt hi)) x z hr)

/-- **The four members after the layers' own rounds keep own**, by number. -/
theorem layersLinkRun_keepsOwn (L : TabLetters) (l : Nat) (hl : l < 24) (he : l % 2 = 0) {x y : ShA}
    (h : (shapeL L).runFrom (14 * l + 5) 4 x = .ok y) : y.1.own = x.1.own := by
  refine runOverCells_keepsOwn L (14 * l + 5) 4 (fun i hi => ?_) x y h
  have ec : TabL.cells L (14 * l + (4 + i) + 1) = (TabL.linkRow L l).at (4 + i) :=
    table_link _ _ _ _ l (4 + i) hl (by omega)
  rw [show 14 * l + 5 + i = 14 * l + (4 + i) + 1 by omega, ec]
  match i, hi with
  | 0, _ => exact readsCell_keepsOwn L l he
  | 1, _ => exact drawCell_keepsOwn L l
  | 2, _ => exact digitsCell_keepsOwn L l
  | 3, _ => exact lookupDigitsCell_keepsOwn L l

/-- **The cell of the layers' own rounds sets the invariant.** -/
theorem ownRoundsCell_laysOwnHeard (L : TabLetters) (g : Nat) {hp : HPlan2} (hG : L.XG.G[g]? =
    some hp)
    (hO : L.k4own g = ownOf (k4Par L.XG hp g)) {x y : ShA} (h : (TabL.k4 L g).1 x = .ok y) :
    OwnRecordHeard L.XG.layers hp g y.1 := by
  unfold TabL.k4 at h
  rw [hG] at h
  have h1 : liftO (k4StepL (L.k4pub g) (L.k4own g) (k4Par L.XG hp g)) x = .ok y := h
  unfold liftO liftQ at h1
  cases hq : optE (k4StepL (L.k4pub g) (L.k4own g) (k4Par L.XG hp g)) x.1 with
  | error e =>
    rw [hq] at h1
    exact nomatch h1
  | ok b =>
    rw [hq] at h1
    obtain rfl : (b, x.2) = y := Except.ok.inj h1
    unfold optE at hq
    split at hq
    · rename_i u hu
      obtain rfl := Except.ok.inj hq
      unfold k4StepL at hu
      split at hu
      · split at hu
        · cases hu
        · split at hu
          · rw [hO, ← k4G_eq] at hu
            exact ownRoundsStep_laysOwnHeard (k4Par L.XG hp g) hu
          · cases hu
      · cases hu
    · cases hq

/-- **The light step at a layers' link's batching.** -/
def layersBatchingLight (L : TabLetters) (l : Nat) : ShA → Except String ShA :=
  match L.k9 l, testsWhere L.XZ l 0, L.XG.G[l / 2]? with
  | some p, some w, some hp =>
    liftQ (batchGSL.1 p.rows w.1 (layersLightRows L.XG (l / 2) (hp.nU.getD 2 0))
      (VerifiableInference.Desc.First.orderOf (subAt l)))
  | _, _, _ => fun _ => .error "the light batching: no numbers"

/-- **Where it returns, the table's cell returns the same**, at the invariant. -/
theorem layersBatchingLight_standsUnder (L : TabLetters) (l : Nat) (hl : l < 24) (he : l % 2 =
    0) {hp : HPlan2}
    (hG : L.XG.G[l / 2]? = some hp) {x y : ShA} (hI : OwnRecordHeard L.XG.layers hp (l / 2) x.1)
    (h : layersBatchingLight L l x = .ok y) : (TabL.batch L l).1 x = .ok y := by
  unfold layersBatchingLight at h
  unfold TabL.batch
  rw [hG] at h
  cases h1 : L.k9 l with
  | none =>
    rw [h1] at h
    exact nomatch h
  | some p =>
    cases h2 : testsWhere L.XZ l 0 with
    | none =>
      rw [h1, h2] at h
      exact nomatch h
    | some w =>
      rw [h1, h2] at h
      have n24 : (l == 24) = false := by simpa using (by omega : l ≠ 24)
      have ev : (l % 2 == 0) = true := by simpa using he
      simp only [n24, ev, if_true, Bool.false_eq_true, if_false]
      have h' : liftQ (batchGSL.1 p.rows w.1 (layersLightRows L.XG (l / 2) (hp.nU.getD 2 0))
          (VerifiableInference.Desc.First.orderOf (subAt l))) x = .ok y := h
      show liftQ (batchGS p.rows w.1 (fun o => (tabOf (rowsLay L.XG (l / 2)) o).g)
          (VerifiableInference.Desc.First.orderOf (subAt l))) x = .ok y
      unfold liftQ at h' ⊢
      rw [← batchGSL.2] at h'
      cases hb : batchGS p.rows w.1 (layersLightRows L.XG (l / 2) (hp.nU.getD 2 0))
          (VerifiableInference.Desc.First.orderOf (subAt l)) x.1 with
      | error e =>
        rw [hb] at h'
        exact nomatch h'
      | ok u =>
        rw [hb] at h'
        rw [layersMemberStep_standsUnder L.XG (l / 2) hp p.rows w.1 _ hI hb]
        exact h'

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.refusingCell_keepsOwn
#print axioms Johnson.AtFull.Shape.readsCell_keepsOwn
#print axioms Johnson.AtFull.Shape.drawCell_keepsOwn
#print axioms Johnson.AtFull.Shape.digitsCell_keepsOwn
#print axioms Johnson.AtFull.Shape.lookupDigitsCell_keepsOwn
#print axioms Johnson.AtFull.Shape.runOverCells_keepsOwn
#print axioms Johnson.AtFull.Shape.layersLinkRun_keepsOwn
#print axioms Johnson.AtFull.Shape.ownRoundsCell_laysOwnHeard
#print axioms Johnson.AtFull.Shape.layersBatchingLight
#print axioms Johnson.AtFull.Shape.layersBatchingLight_standsUnder
