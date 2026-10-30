-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/ScaledGramTestOfStretchNumbers.lean

The test that stretch numbers hold, in a form that keeps its own numbers small: the test of
IntegerModel/Bounds/GramTestOfStretchNumbers.lean with `scaledGramIterationFits`
(IntegerModel/Bounds/ScaledGramIteration.lean) in the place of `gramIterationFits`.
- `stretchBound_of_scaledGramIterationFits`: a matrix that passes `scaledGramIterationFits` with the
  number `stretch` and any levels has `StretchBound` with that number.
- `StretchLevels`: a list of levels for each matrix that has a number in a `StretchNumbers`.
- `stretchNumbersPassScaledGramTest settings weights levels numbers`: `scaledGramIterationFits` at
  each matrix and number that `StretchNumbers.Hold` (IntegerModel/Bounds/LengthCheck.lean) names, at
  the same sizes, with that matrix's levels.
- `hold_of_stretchNumbersPassScaledGramTest`: numbers that pass hold.
- `allConditionsHold_of_stretchNumbersPassScaledGramTest`: for settings, tables and weights that fit
  together (`wellFormed`), and stretch numbers that pass `stretchNumbersPassScaledGramTest` with
  some levels and with which they pass `lengthWorstCaseCheck`, all range conditions hold at all
  positions of every prompt. Its three premises on the settings, tables, weights, levels and numbers
  are values of Boolean functions.
- `stretchNumbersPassScaledGramTest_noLevels`: with no level anywhere the test is
  `stretchNumbersPassGramTest` without a squaring.
Limits: those at the heads of IntegerModel/Bounds/ScaledGramIteration.lean and
IntegerModel/Bounds/LengthCheck.lean. The tests are sufficient, not necessary. The stretch numbers
and the levels are given, not computed here; nothing is asked of where they come from. This file
says of no weights, no numbers and no levels that they pass, but for the small made-up weights of
its examples. It imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.ScaledGramIteration
import IntegerModel.Bounds.GramTestOfStretchNumbers

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-- **A matrix that passes the scaled Gram test stretches no vector by more than `stretch`.** -/
theorem stretchBound_of_scaledGramIterationFits (W : Matrix) (rows columns : Nat)
    (levels : List ScaledLevel) (stretch : Int)
    (fits : scaledGramIterationFits W rows columns levels stretch = true) :
    StretchBound W rows columns stretch :=
  stretchBoundOf_of_scaledGramIterationFitsOf (fun row column => (W.entry row).entry column) rows
    columns levels stretch fits

/-- The levels for each matrix that has a number in a `StretchNumbers`. -/
structure StretchLevels where
  output : Nat → List ScaledLevel            -- by layer: Wo
  up : Nat → List ScaledLevel                -- by layer: Wu of the dense block or the shared expert
  down : Nat → List ScaledLevel              -- by layer: Wd of the dense block or the shared expert
  routedUp : Nat → Nat → List ScaledLevel    -- by layer and expert: Wur_e
  routedDown : Nat → Nat → List ScaledLevel  -- by layer and expert: Wdr_e

/-- No level for any matrix. -/
def noLevels : StretchLevels where
  output _ := []
  up _ := []
  down _ := []
  routedUp _ _ := []
  routedDown _ _ := []

/-- **The scaled Gram test of the stretch numbers.** Does each matrix that the check treats by
lengths pass `scaledGramIterationFits`, with its levels and its stretch number? -/
def stretchNumbersPassScaledGramTest (settings : Settings) (weights : Weights)
    (levels : StretchLevels) (numbers : StretchNumbers) : Bool :=
  allBelow settings.layers fun layer =>
    scaledGramIterationFits (weights.perLayer.entry layer).output settings.queryWidth settings.width
      (levels.output layer) (numbers.output layer)
    && scaledGramIterationFits (weights.perLayer.entry layer).shared.up settings.width
      (sharedHidden settings layer) (levels.up layer) (numbers.up layer)
    && scaledGramIterationFits (weights.perLayer.entry layer).shared.down
      (sharedHidden settings layer) settings.width (levels.down layer) (numbers.down layer)
    && (!settings.isMixture layer || allBelow settings.experts fun expert =>
      scaledGramIterationFits ((weights.perLayer.entry layer).routed.entry expert).up settings.width
        settings.expertHidden (levels.routedUp layer expert) (numbers.routedUp layer expert)
      && scaledGramIterationFits ((weights.perLayer.entry layer).routed.entry expert).down
        settings.expertHidden settings.width (levels.routedDown layer expert)
        (numbers.routedDown layer expert))

/-- **Stretch numbers that pass the scaled Gram test hold.** -/
theorem hold_of_stretchNumbersPassScaledGramTest (s : Settings) (weights : Weights)
    (levels : StretchLevels) (numbers : StretchNumbers)
    (fits : stretchNumbersPassScaledGramTest s weights levels numbers = true) :
    numbers.Hold s weights := by
  simp only [stretchNumbersPassScaledGramTest, allBelow_spec, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at fits
  intro l inLayers
  have layerFits := fits l inLayers
  refine ⟨stretchBound_of_scaledGramIterationFits _ _ _ _ _ layerFits.1.1.1,
    stretchBound_of_scaledGramIterationFits _ _ _ _ _ layerFits.1.1.2,
    stretchBound_of_scaledGramIterationFits _ _ _ _ _ layerFits.1.2,
    fun mixture e inExperts => ?_⟩
  rcases layerFits.2 with dense | routed
  · rw [mixture] at dense
    exact absurd dense (by decide)
  · exact ⟨stretchBound_of_scaledGramIterationFits _ _ _ _ _ (routed e inExperts).1,
      stretchBound_of_scaledGramIterationFits _ _ _ _ _ (routed e inExperts).2⟩

/-- **Weights that pass the length check with stretch numbers that pass the scaled Gram test never
fail a range condition.** For settings, tables and weights that fit together, all range conditions
hold at all positions of every prompt. -/
theorem allConditionsHold_of_stretchNumbersPassScaledGramTest (s : Settings) (tables : Tables)
    (weights : Weights) (levels : StretchLevels) (numbers : StretchNumbers)
    (formed : wellFormed s tables weights = true)
    (fits : stretchNumbersPassScaledGramTest s weights levels numbers = true)
    (passes : lengthWorstCaseCheck s tables weights numbers = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) :
    allConditionsHold s (trace s tables weights prompt) = true :=
  allConditionsHold_of_lengthWorstCaseCheck s tables weights numbers formed
    (hold_of_stretchNumbersPassScaledGramTest s weights levels numbers fits) passes prompt prompt_ok

/-- With no level anywhere the test is the exact test without a squaring. -/
theorem stretchNumbersPassScaledGramTest_noLevels (s : Settings) (weights : Weights)
    (numbers : StretchNumbers) :
    stretchNumbersPassScaledGramTest s weights noLevels numbers =
      stretchNumbersPassGramTest s weights 0 numbers := by
  simp only [stretchNumbersPassScaledGramTest, stretchNumbersPassGramTest, noLevels,
    scaledGramIterationFits_nil]

/-! ## The test on small weights

Two layers of width 2, the second a mixture layer with one routed expert. Each of the matrices that
the test reads has the rows (300, 0) and (0, 400), which stretch by 400 at most. With the one level
of IntegerModel/Bounds/ScaledGramIteration.lean, part 5, the number 405 passes and 404 does not.
With 405 everywhere the numbers pass. With 404 at any one of the five kinds of number they do not,
so each kind is tested. With no level at one kind of matrix 405 does not pass there either, so the
levels are read. -/

/-- The settings of the small weights. Only the sizes are read. -/
private def smallSettings : Settings :=
  { (default : Settings) with
    layers := 2, width := 2, queryHeads := 1, headDim := 2, hidden := 2, expertHidden := 2,
    experts := 1 }

/-- The matrix with the rows (300, 0) and (0, 400). -/
private def smallMatrix : Matrix := #[#[300, 0], #[0, 400]]

/-- The small weights: the same matrix at every place that the test reads. -/
private def smallWeights : Weights :=
  let block : GatedWeights :=
    { (default : GatedWeights) with up := smallMatrix, down := smallMatrix }
  let layer : LayerWeights :=
    { (default : LayerWeights) with output := smallMatrix, shared := block, routed := #[block] }
  { (default : Weights) with perLayer := #[layer, layer] }

/-- One level for the small matrix: its product with its transpose, divided by 7 and rounded. -/
private def smallLevel : List ScaledLevel :=
  [⟨fun row column => if row = column then (if row = 0 then 12857 else 22857) else 0, 7, 2, 23409⟩]

/-- That level at every matrix. -/
private def smallLevels : StretchLevels :=
  ⟨fun _ => smallLevel, fun _ => smallLevel, fun _ => smallLevel, fun _ _ => smallLevel,
    fun _ _ => smallLevel⟩

example : stretchNumbersPassScaledGramTest smallSettings smallWeights smallLevels
    ⟨fun _ => 405, fun _ => 405, fun _ => 405, fun _ _ => 405, fun _ _ => 405⟩ = true := by decide
example : stretchNumbersPassScaledGramTest smallSettings smallWeights smallLevels
    ⟨fun _ => 404, fun _ => 405, fun _ => 405, fun _ _ => 405, fun _ _ => 405⟩ = false := by decide
example : stretchNumbersPassScaledGramTest smallSettings smallWeights smallLevels
    ⟨fun _ => 405, fun _ => 404, fun _ => 405, fun _ _ => 405, fun _ _ => 405⟩ = false := by decide
example : stretchNumbersPassScaledGramTest smallSettings smallWeights smallLevels
    ⟨fun _ => 405, fun _ => 405, fun _ => 404, fun _ _ => 405, fun _ _ => 405⟩ = false := by decide
example : stretchNumbersPassScaledGramTest smallSettings smallWeights smallLevels
    ⟨fun _ => 405, fun _ => 405, fun _ => 405, fun _ _ => 404, fun _ _ => 405⟩ = false := by decide
example : stretchNumbersPassScaledGramTest smallSettings smallWeights smallLevels
    ⟨fun _ => 405, fun _ => 405, fun _ => 405, fun _ _ => 405, fun _ _ => 404⟩ = false := by decide
example : stretchNumbersPassScaledGramTest smallSettings smallWeights
    { smallLevels with routedDown := fun _ _ => [] }
    ⟨fun _ => 405, fun _ => 405, fun _ => 405, fun _ _ => 405, fun _ _ => 405⟩ = false := by decide

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.stretchBound_of_scaledGramIterationFits
#print axioms IntegerTransformer.Bounds.hold_of_stretchNumbersPassScaledGramTest
#print axioms IntegerTransformer.Bounds.allConditionsHold_of_stretchNumbersPassScaledGramTest
#print axioms IntegerTransformer.Bounds.stretchNumbersPassScaledGramTest_noLevels
