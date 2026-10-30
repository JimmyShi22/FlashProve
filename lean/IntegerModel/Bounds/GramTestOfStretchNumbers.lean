-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/GramTestOfStretchNumbers.lean

A test that stretch numbers hold, so that the length check rests on tests alone.
- `stretchBound_of_gramIterationFits`: a matrix that passes `gramIterationFits`
  (IntegerModel/Bounds/GramIteration.lean) with the number `stretch` has `StretchBound` with it.
  `StretchBound` of an array of rows is `StretchBoundOf` of its entries, by unfolding.
- `stretchNumbersPassGramTest settings weights steps numbers`: `gramIterationFits`, with `steps`
  squarings, at each matrix and number that `StretchNumbers.Hold`
  (IntegerModel/Bounds/LengthCheck.lean) names, at the same sizes: in every layer the output matrix
  of attention and the up and down matrices of the dense block or the shared expert; in a mixture
  layer also the up and down matrices of every routed expert.
- `hold_of_stretchNumbersPassGramTest`: numbers that pass hold.
- `allConditionsHold_of_stretchNumbersPassGramTest`: for settings, tables and weights that fit
  together (`wellFormed`), and stretch numbers that pass `stretchNumbersPassGramTest` and with which
  they pass `lengthWorstCaseCheck`, all range conditions hold at all positions of every prompt. Its
  three premises on the settings, tables, weights and numbers are values of Boolean functions.
Limits: those at the heads of IntegerModel/Bounds/GramIteration.lean and
IntegerModel/Bounds/LengthCheck.lean. The tests are sufficient, not necessary, and
`stretchNumbersPassGramTest` is costly to evaluate. The stretch numbers are given, not computed
here. This file says of no weights and of no numbers that they pass, but for the small made-up
weights of its examples. It imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.GramIteration
import IntegerModel.Bounds.LengthNeverFails

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-- **A matrix that passes the Gram test stretches no vector by more than `stretch`.** -/
theorem stretchBound_of_gramIterationFits (W : Matrix) (rows columns steps : Nat) (stretch : Int)
    (fits : gramIterationFits W rows columns steps stretch = true) :
    StretchBound W rows columns stretch :=
  stretchBoundOf_of_gramIterationFitsOf (fun row column => (W.entry row).entry column) rows columns
    steps stretch fits

/-- **The Gram test of the stretch numbers.** Does each matrix that the check treats by lengths pass
`gramIterationFits`, with `steps` squarings, with its stretch number? -/
def stretchNumbersPassGramTest (settings : Settings) (weights : Weights) (steps : Nat)
    (numbers : StretchNumbers) : Bool :=
  allBelow settings.layers fun layer =>
    gramIterationFits (weights.perLayer.entry layer).output settings.queryWidth settings.width steps
      (numbers.output layer)
    && gramIterationFits (weights.perLayer.entry layer).shared.up settings.width
      (sharedHidden settings layer) steps (numbers.up layer)
    && gramIterationFits (weights.perLayer.entry layer).shared.down (sharedHidden settings layer)
      settings.width steps (numbers.down layer)
    && (!settings.isMixture layer || allBelow settings.experts fun expert =>
      gramIterationFits ((weights.perLayer.entry layer).routed.entry expert).up settings.width
        settings.expertHidden steps (numbers.routedUp layer expert)
      && gramIterationFits ((weights.perLayer.entry layer).routed.entry expert).down
        settings.expertHidden settings.width steps (numbers.routedDown layer expert))

/-- **Stretch numbers that pass the Gram test hold.** -/
theorem hold_of_stretchNumbersPassGramTest (s : Settings) (weights : Weights) (steps : Nat)
    (numbers : StretchNumbers)
    (fits : stretchNumbersPassGramTest s weights steps numbers = true) :
    numbers.Hold s weights := by
  simp only [stretchNumbersPassGramTest, allBelow_spec, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at fits
  intro l inLayers
  have layerFits := fits l inLayers
  refine ⟨stretchBound_of_gramIterationFits _ _ _ steps _ layerFits.1.1.1,
    stretchBound_of_gramIterationFits _ _ _ steps _ layerFits.1.1.2,
    stretchBound_of_gramIterationFits _ _ _ steps _ layerFits.1.2, fun mixture e inExperts => ?_⟩
  rcases layerFits.2 with dense | routed
  · rw [mixture] at dense
    exact absurd dense (by decide)
  · exact ⟨stretchBound_of_gramIterationFits _ _ _ steps _ (routed e inExperts).1,
      stretchBound_of_gramIterationFits _ _ _ steps _ (routed e inExperts).2⟩

/-- **Weights that pass the length check with stretch numbers that pass the Gram test never fail a
range condition.** For settings, tables and weights that fit together, all range conditions hold at
all positions of every prompt. -/
theorem allConditionsHold_of_stretchNumbersPassGramTest (s : Settings) (tables : Tables)
    (weights : Weights) (steps : Nat) (numbers : StretchNumbers)
    (formed : wellFormed s tables weights = true)
    (fits : stretchNumbersPassGramTest s weights steps numbers = true)
    (passes : lengthWorstCaseCheck s tables weights numbers = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) :
    allConditionsHold s (trace s tables weights prompt) = true :=
  allConditionsHold_of_lengthWorstCaseCheck s tables weights numbers formed
    (hold_of_stretchNumbersPassGramTest s weights steps numbers fits) passes prompt prompt_ok

/-! ## The test on small weights

Two layers of width 2, the second a mixture layer with one routed expert. Each of the matrices that
the test reads has the rows (30, 0) and (0, 40), which stretch by 40 at most. After one squaring the
number 41 passes (IntegerModel/Bounds/GramIteration.lean, part 5) and 40 does not. With 41
everywhere the numbers pass. With 40 at any one of the five kinds of number they do not, so each
kind is tested. -/

/-- The settings of the small weights. Only the sizes are read. -/
private def smallSettings : Settings :=
  { (default : Settings) with
    layers := 2, width := 2, queryHeads := 1, headDim := 2, hidden := 2, expertHidden := 2,
    experts := 1 }

/-- The matrix with the rows (30, 0) and (0, 40). -/
private def smallMatrix : Matrix := #[#[30, 0], #[0, 40]]

/-- The small weights: the same matrix at every place that the test reads. -/
private def smallWeights : Weights :=
  let block : GatedWeights :=
    { (default : GatedWeights) with up := smallMatrix, down := smallMatrix }
  let layer : LayerWeights :=
    { (default : LayerWeights) with output := smallMatrix, shared := block, routed := #[block] }
  { (default : Weights) with perLayer := #[layer, layer] }

example : stretchNumbersPassGramTest smallSettings smallWeights 1
    ⟨fun _ => 41, fun _ => 41, fun _ => 41, fun _ _ => 41, fun _ _ => 41⟩ = true := by decide
example : stretchNumbersPassGramTest smallSettings smallWeights 1
    ⟨fun _ => 40, fun _ => 41, fun _ => 41, fun _ _ => 41, fun _ _ => 41⟩ = false := by decide
example : stretchNumbersPassGramTest smallSettings smallWeights 1
    ⟨fun _ => 41, fun _ => 40, fun _ => 41, fun _ _ => 41, fun _ _ => 41⟩ = false := by decide
example : stretchNumbersPassGramTest smallSettings smallWeights 1
    ⟨fun _ => 41, fun _ => 41, fun _ => 40, fun _ _ => 41, fun _ _ => 41⟩ = false := by decide
example : stretchNumbersPassGramTest smallSettings smallWeights 1
    ⟨fun _ => 41, fun _ => 41, fun _ => 41, fun _ _ => 40, fun _ _ => 41⟩ = false := by decide
example : stretchNumbersPassGramTest smallSettings smallWeights 1
    ⟨fun _ => 41, fun _ => 41, fun _ => 41, fun _ _ => 41, fun _ _ => 40⟩ = false := by decide

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.stretchBound_of_gramIterationFits
#print axioms IntegerTransformer.Bounds.hold_of_stretchNumbersPassGramTest
#print axioms IntegerTransformer.Bounds.allConditionsHold_of_stretchNumbersPassGramTest
