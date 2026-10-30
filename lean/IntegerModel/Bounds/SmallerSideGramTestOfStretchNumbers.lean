-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/SmallerSideGramTestOfStretchNumbers.lean

The test of IntegerModel/Bounds/ScaledGramTestOfStretchNumbers.lean, with each matrix tested on its
smaller side (IntegerModel/Bounds/StretchOfTranspose.lean).
- `scaledGramIterationFitsOnSmallerSide matrix rows columns levels stretch`: the scaled test on the
  smaller side, for the entries of an array of rows; with
  `stretchBound_of_scaledGramIterationFitsOnSmallerSide`.
- `stretchNumbersPassSmallerSideGramTest settings weights levels numbers`: that test at each matrix
  and number that `StretchNumbers.Hold` (IntegerModel/Bounds/LengthCheck.lean) names, at the same
  sizes, with that matrix's levels.
- `hold_of_stretchNumbersPassSmallerSideGramTest`: numbers that pass hold.
- `allConditionsHold_of_stretchNumbersPassSmallerSideGramTest`: for settings, tables and weights
  that fit together (`wellFormed`), and stretch numbers that pass the test with some levels and with
  which they pass `lengthWorstCaseCheck`, all range conditions hold at all positions of every
  prompt. Its three premises on the settings, tables, weights, levels and numbers are values of
  Boolean functions.
What it buys: where a block has more hidden units than the stream is wide, as at the sizes of
VerifiableInference/ModelWeights.lean, a down matrix has more rows than columns, so its test works
on a square matrix of the stream's width and not of the number of hidden units.
Limits: those at the heads of the two files named above and of IntegerModel/Bounds/LengthCheck.lean.
The levels of a matrix belong to its smaller side. The stretch numbers and the levels are given, not
computed here. This file says of no weights, no numbers and no levels that they pass, but for the
small made-up weights of its examples. It imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.StretchOfTranspose
import IntegerModel.Bounds.ScaledGramTestOfStretchNumbers

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-- The scaled Gram test on the smaller side, for the matrix whose rows are the entries of the array
`matrix`. -/
def scaledGramIterationFitsOnSmallerSide (matrix : Matrix) (rows columns : Nat)
    (levels : List ScaledLevel) (stretch : Int) : Bool :=
  scaledGramIterationFitsOnSmallerSideOf (fun row column => (matrix.entry row).entry column)
    rows columns levels stretch

/-- **A matrix that passes the test on its smaller side stretches no vector by more than
`stretch`.** -/
theorem stretchBound_of_scaledGramIterationFitsOnSmallerSide (W : Matrix) (rows columns : Nat)
    (levels : List ScaledLevel) (stretch : Int)
    (fits : scaledGramIterationFitsOnSmallerSide W rows columns levels stretch = true) :
    StretchBound W rows columns stretch :=
  stretchBoundOf_of_scaledGramIterationFitsOnSmallerSideOf
    (fun row column => (W.entry row).entry column) rows columns levels stretch fits

/-- **The scaled Gram test of the stretch numbers, on the smaller side.** Does each matrix that the
check treats by lengths pass the scaled test on its smaller side, with its levels and its stretch
number? -/
def stretchNumbersPassSmallerSideGramTest (settings : Settings) (weights : Weights)
    (levels : StretchLevels) (numbers : StretchNumbers) : Bool :=
  allBelow settings.layers fun layer =>
    scaledGramIterationFitsOnSmallerSide (weights.perLayer.entry layer).output settings.queryWidth
      settings.width (levels.output layer) (numbers.output layer)
    && scaledGramIterationFitsOnSmallerSide (weights.perLayer.entry layer).shared.up settings.width
      (sharedHidden settings layer) (levels.up layer) (numbers.up layer)
    && scaledGramIterationFitsOnSmallerSide (weights.perLayer.entry layer).shared.down
      (sharedHidden settings layer) settings.width (levels.down layer) (numbers.down layer)
    && (!settings.isMixture layer || allBelow settings.experts fun expert =>
      scaledGramIterationFitsOnSmallerSide ((weights.perLayer.entry layer).routed.entry expert).up
        settings.width settings.expertHidden (levels.routedUp layer expert)
        (numbers.routedUp layer expert)
      && scaledGramIterationFitsOnSmallerSide
        ((weights.perLayer.entry layer).routed.entry expert).down settings.expertHidden
        settings.width (levels.routedDown layer expert) (numbers.routedDown layer expert))

/-- **Stretch numbers that pass the scaled Gram test on the smaller side hold.** -/
theorem hold_of_stretchNumbersPassSmallerSideGramTest (s : Settings) (weights : Weights)
    (levels : StretchLevels) (numbers : StretchNumbers)
    (fits : stretchNumbersPassSmallerSideGramTest s weights levels numbers = true) :
    numbers.Hold s weights := by
  simp only [stretchNumbersPassSmallerSideGramTest, allBelow_spec, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at fits
  intro l inLayers
  have layerFits := fits l inLayers
  refine ⟨stretchBound_of_scaledGramIterationFitsOnSmallerSide _ _ _ _ _ layerFits.1.1.1,
    stretchBound_of_scaledGramIterationFitsOnSmallerSide _ _ _ _ _ layerFits.1.1.2,
    stretchBound_of_scaledGramIterationFitsOnSmallerSide _ _ _ _ _ layerFits.1.2,
    fun mixture e inExperts => ?_⟩
  rcases layerFits.2 with dense | routed
  · rw [mixture] at dense
    exact absurd dense (by decide)
  · exact ⟨stretchBound_of_scaledGramIterationFitsOnSmallerSide _ _ _ _ _ (routed e inExperts).1,
      stretchBound_of_scaledGramIterationFitsOnSmallerSide _ _ _ _ _ (routed e inExperts).2⟩

/-- **Weights that pass the length check with stretch numbers that pass the scaled Gram test on the
smaller side never fail a range condition.** For settings, tables and weights that fit together, all
range conditions hold at all positions of every prompt. -/
theorem allConditionsHold_of_stretchNumbersPassSmallerSideGramTest (s : Settings) (tables : Tables)
    (weights : Weights) (levels : StretchLevels) (numbers : StretchNumbers)
    (formed : wellFormed s tables weights = true)
    (fits : stretchNumbersPassSmallerSideGramTest s weights levels numbers = true)
    (passes : lengthWorstCaseCheck s tables weights numbers = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) :
    allConditionsHold s (trace s tables weights prompt) = true :=
  allConditionsHold_of_lengthWorstCaseCheck s tables weights numbers formed
    (hold_of_stretchNumbersPassSmallerSideGramTest s weights levels numbers fits) passes prompt
    prompt_ok

/-! ## The test on small weights

Two layers, the second a mixture layer with one routed expert; the stream has width 1, the query
heads together have 3 entries, and each block has 3 hidden units. The output matrix and the down
matrices have the three rows (2), (3), (6); the up matrices have the one row (2, 3, 6). Each
stretches by 7, and each has a smaller side of 1. With no level and 7 everywhere the numbers pass.
With 6 at any one of the five kinds of number they do not, so each kind is tested.

With no level the test gives the same answer on either side of a matrix; no theorem here says so. So
these six examples do not see the side. Two more do. They have one level for every matrix, which
fits the side with one entry, 49: the matrix (7), the scale 7, the error 0, the bound 7. With 7
everywhere the test on the smaller side says yes. `stretchNumbersPassScaledGramTest`, which takes
the side of the rows, says no with the same levels: the output matrix has three rows. -/

/-- The settings of the small weights. Only the sizes are read. -/
private def smallSettings : Settings :=
  { (default : Settings) with
    layers := 2, width := 1, queryHeads := 1, headDim := 3, hidden := 3, expertHidden := 3,
    experts := 1 }

/-- The small weights. -/
private def smallWeights : Weights :=
  let block : GatedWeights :=
    { (default : GatedWeights) with up := #[#[2, 3, 6]], down := #[#[2], #[3], #[6]] }
  let layer : LayerWeights :=
    { (default : LayerWeights) with
      output := #[#[2], #[3], #[6]], shared := block, routed := #[block] }
  { (default : Weights) with perLayer := #[layer, layer] }

example : stretchNumbersPassSmallerSideGramTest smallSettings smallWeights noLevels
    ⟨fun _ => 7, fun _ => 7, fun _ => 7, fun _ _ => 7, fun _ _ => 7⟩ = true := by decide
example : stretchNumbersPassSmallerSideGramTest smallSettings smallWeights noLevels
    ⟨fun _ => 6, fun _ => 7, fun _ => 7, fun _ _ => 7, fun _ _ => 7⟩ = false := by decide
example : stretchNumbersPassSmallerSideGramTest smallSettings smallWeights noLevels
    ⟨fun _ => 7, fun _ => 6, fun _ => 7, fun _ _ => 7, fun _ _ => 7⟩ = false := by decide
example : stretchNumbersPassSmallerSideGramTest smallSettings smallWeights noLevels
    ⟨fun _ => 7, fun _ => 7, fun _ => 6, fun _ _ => 7, fun _ _ => 7⟩ = false := by decide
example : stretchNumbersPassSmallerSideGramTest smallSettings smallWeights noLevels
    ⟨fun _ => 7, fun _ => 7, fun _ => 7, fun _ _ => 6, fun _ _ => 7⟩ = false := by decide
example : stretchNumbersPassSmallerSideGramTest smallSettings smallWeights noLevels
    ⟨fun _ => 7, fun _ => 7, fun _ => 7, fun _ _ => 7, fun _ _ => 6⟩ = false := by decide

/-- One level for every matrix: the matrix (7), the scale 7, the error 0, the bound 7. -/
private def oneLevelEverywhere : StretchLevels where
  output _ := [⟨fun _ _ => 7, 7, 0, 7⟩]
  up _ := [⟨fun _ _ => 7, 7, 0, 7⟩]
  down _ := [⟨fun _ _ => 7, 7, 0, 7⟩]
  routedUp _ _ := [⟨fun _ _ => 7, 7, 0, 7⟩]
  routedDown _ _ := [⟨fun _ _ => 7, 7, 0, 7⟩]

example : stretchNumbersPassSmallerSideGramTest smallSettings smallWeights oneLevelEverywhere
    ⟨fun _ => 7, fun _ => 7, fun _ => 7, fun _ _ => 7, fun _ _ => 7⟩ = true := by decide
example : stretchNumbersPassScaledGramTest smallSettings smallWeights oneLevelEverywhere
    ⟨fun _ => 7, fun _ => 7, fun _ => 7, fun _ _ => 7, fun _ _ => 7⟩ = false := by decide

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.stretchBound_of_scaledGramIterationFitsOnSmallerSide
#print axioms IntegerTransformer.Bounds.hold_of_stretchNumbersPassSmallerSideGramTest
#print axioms IntegerTransformer.Bounds.allConditionsHold_of_stretchNumbersPassSmallerSideGramTest
