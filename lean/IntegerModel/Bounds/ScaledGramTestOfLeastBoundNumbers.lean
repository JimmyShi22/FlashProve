-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/ScaledGramTestOfLeastBoundNumbers.lean

A test that the numbers of `leastBoundWorstCaseCheck` hold, so that the check rests on tests alone.
- `LeastBoundLevels`: for each number of a `LeastBoundNumbers` a list of given levels
  (`ScaledLevel`, IntegerModel/Bounds/ScaledGramIteration.lean). The empty list is allowed.
- `gatedStretchFits`: `scaledGramIterationFitsOf` at the three matrices of one gated block that
  `GatedStretchNumbersHold` names: the up matrix, the up matrix with scaled columns, the down
  matrix.
- `leastBoundNumbersPassScaledGramTest settings tables weights numbers levels`: the same test at
  each matrix and number that `LeastBoundNumbers.Hold` (IntegerModel/Bounds/LeastBoundCheck.lean)
  names, at the same sizes.
- `hold_of_leastBoundNumbersPassScaledGramTest`: numbers that pass hold.
- `allConditionsHold_of_leastBoundNumbersPassScaledGramTest`: for settings, tables and weights that
  fit together (`wellFormed`), and numbers that pass this test and with which they pass
  `leastBoundWorstCaseCheck`, all range conditions hold at all positions of every prompt. Its three
  premises on the settings, tables, weights, numbers and levels are values of Boolean functions.
Limits: those at the heads of IntegerModel/Bounds/ScaledGramIteration.lean and
IntegerModel/Bounds/LeastBoundCheck.lean. The tests are sufficient, not necessary. Each matrix is
tested on the side of its rows; a test on the smaller side, which
IntegerModel/Bounds/StretchOfTranspose.lean allows, is not offered here. The numbers and the levels
are given, not computed here. This file says of no weights, of no numbers and of no levels that they
pass, but for the small made-up weights of its examples. It imports Lean's core and the model's own
files.
-/
import IntegerModel.Bounds.LeastBoundNeverFails

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-- For each number of a `LeastBoundNumbers`, the given levels with which it is tested. -/
structure LeastBoundLevels where
  output : Nat → List ScaledLevel                -- by layer
  valueHead : Nat → Nat → List ScaledLevel       -- by layer and key-value head
  up : Nat → List ScaledLevel                    -- by layer
  scaledUp : Nat → List ScaledLevel              -- by layer
  down : Nat → List ScaledLevel                  -- by layer
  routedUp : Nat → Nat → List ScaledLevel        -- by layer and expert
  routedScaledUp : Nat → Nat → List ScaledLevel  -- by layer and expert
  routedDown : Nat → Nat → List ScaledLevel      -- by layer and expert

/-- The entries of a matrix that is given as an array of rows. -/
def entriesOfMatrix (matrix : Matrix) (row column : Nat) : Int := (matrix.entry row).entry column

/-- The test of the three numbers of one gated block. -/
def gatedStretchFits (tables : Tables) (gatedWeights : GatedWeights) (width hidden gateShift : Nat)
    (taus : List Int) (ball : Ball) (stretchUp stretchScaledUp stretchDown : Int)
    (levelsUp levelsScaledUp levelsDown : List ScaledLevel) : Bool :=
  scaledGramIterationFitsOf (entriesOfMatrix gatedWeights.up) width hidden levelsUp stretchUp
  && scaledGramIterationFitsOf (scaledUpEntries tables gatedWeights width gateShift taus ball) width
    hidden levelsScaledUp stretchScaledUp
  && scaledGramIterationFitsOf (entriesOfMatrix gatedWeights.down) hidden width levelsDown
    stretchDown

/-- The three numbers of a gated block that passes the test are what they are said to be. -/
theorem gatedStretchNumbersHold_of_fits (tables : Tables) (w : GatedWeights)
    (width hidden gateShift : Nat) (taus : List Int) (ball : Ball)
    (stretchUp stretchScaledUp stretchDown : Int)
    (levelsUp levelsScaledUp levelsDown : List ScaledLevel)
    (fits : gatedStretchFits tables w width hidden gateShift taus ball stretchUp stretchScaledUp
      stretchDown levelsUp levelsScaledUp levelsDown = true) :
    GatedStretchNumbersHold tables w width hidden gateShift taus ball stretchUp stretchScaledUp
      stretchDown := by
  simp only [gatedStretchFits, Bool.and_eq_true] at fits
  exact ⟨stretchBoundOf_of_scaledGramIterationFitsOf _ _ _ _ _ fits.1.1,
    stretchBoundOf_of_scaledGramIterationFitsOf _ _ _ _ _ fits.1.2,
    stretchBoundOf_of_scaledGramIterationFitsOf _ _ _ _ _ fits.2⟩

/-- **The scaled Gram test of the least-bound check's numbers.** Does each matrix that the check
treats by lengths pass `scaledGramIterationFitsOf`, with its levels, with its stretch number? -/
def leastBoundNumbersPassScaledGramTest (settings : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) (levels : LeastBoundLevels) : Bool :=
  allBelow settings.layers fun layer =>
    scaledGramIterationFitsOf (entriesOfMatrix (weights.perLayer.entry layer).output)
      settings.queryWidth settings.width (levels.output layer) (numbers.output layer)
    && (allBelow settings.keyValueHeads fun keyValueHead =>
      scaledGramIterationFitsOf
        (fun row coordinate => ((weights.perLayer.entry layer).value.entry row).entry
          (keyValueHead * settings.headDim + coordinate))
        settings.width settings.headDim (levels.valueHead layer keyValueHead)
        (numbers.valueHead layer keyValueHead))
    && gatedStretchFits tables (weights.perLayer.entry layer).shared settings.width
      (sharedHidden settings layer) (settings.perLayer.entry layer).gateShift numbers.taus
      (feedForwardBall settings layer
        (leastStreamLengthAfterAttention settings tables weights numbers layer))
      (numbers.up layer) (numbers.scaledUp layer) (numbers.down layer)
      (levels.up layer) (levels.scaledUp layer) (levels.down layer)
    && (!settings.isMixture layer || allBelow settings.experts fun expert =>
      gatedStretchFits tables ((weights.perLayer.entry layer).routed.entry expert) settings.width
        settings.expertHidden (settings.perLayer.entry layer).routedGateShift numbers.taus
        (feedForwardBall settings layer
          (leastStreamLengthAfterAttention settings tables weights numbers layer))
        (numbers.routedUp layer expert) (numbers.routedScaledUp layer expert)
        (numbers.routedDown layer expert)
        (levels.routedUp layer expert) (levels.routedScaledUp layer expert)
        (levels.routedDown layer expert))

/-- **The least-bound check's numbers that pass the scaled Gram test hold.** -/
theorem hold_of_leastBoundNumbersPassScaledGramTest (s : Settings) (tables : Tables)
    (weights : Weights) (numbers : LeastBoundNumbers) (levels : LeastBoundLevels)
    (fits : leastBoundNumbersPassScaledGramTest s tables weights numbers levels = true) :
    numbers.Hold s tables weights := by
  simp only [leastBoundNumbersPassScaledGramTest, allBelow_spec, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at fits
  intro l inLayers
  have layerFits := fits l inLayers
  refine ⟨stretchBoundOf_of_scaledGramIterationFitsOf _ _ _ _ _ layerFits.1.1.1,
    fun g inHeads => stretchBoundOf_of_scaledGramIterationFitsOf _ _ _ _ _
      (layerFits.1.1.2 g inHeads),
    gatedStretchNumbersHold_of_fits _ _ _ _ _ _ _ _ _ _ _ _ _ layerFits.1.2,
    fun mixture e inExperts => ?_⟩
  rcases layerFits.2 with dense | routed
  · rw [mixture] at dense
    exact absurd dense (by decide)
  · exact gatedStretchNumbersHold_of_fits _ _ _ _ _ _ _ _ _ _ _ _ _ (routed e inExperts)

/-- **Weights that pass the least-bound check with numbers that pass the scaled Gram test never fail
a range condition.** For settings, tables and weights that fit together, all range conditions hold
at all positions of every prompt. -/
theorem allConditionsHold_of_leastBoundNumbersPassScaledGramTest (s : Settings) (tables : Tables)
    (weights : Weights) (numbers : LeastBoundNumbers) (levels : LeastBoundLevels)
    (formed : wellFormed s tables weights = true)
    (fits : leastBoundNumbersPassScaledGramTest s tables weights numbers levels = true)
    (passes : leastBoundWorstCaseCheck s tables weights numbers = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) :
    allConditionsHold s (trace s tables weights prompt) = true :=
  allConditionsHold_of_leastBoundWorstCaseCheck s tables weights numbers formed
    (hold_of_leastBoundNumbersPassScaledGramTest s tables weights numbers levels fits) passes prompt
    prompt_ok

/-! ## The test on small weights

Two layers of width 2, the second a mixture layer with one routed expert; one key-value head of two
entries. Each matrix of the weights whose stretch is tested has the rows (30, 0) and (0, 40), which
stretch by 40 at most. The SiLU table has the entry 2 at the three keys that a gate of zeros
can reach, so the up matrix with scaled columns has the rows (60, 0) and (0, 80). With no level the
test is the Gram test without a squaring (IntegerModel/Bounds/ScaledGramIteration.lean): at the
first matrix 43 passes and 42 does not, at the second 86 passes and 85 does not. With 43, and 86 at
the two kinds of number for scaled columns, the numbers pass. With one less at any one of the eight
kinds they do not, so each kind is tested. With 43 at either kind for scaled columns they do not, so
the scale is read. -/

/-- The settings of the small weights. -/
private def smallSettings : Settings :=
  { (default : Settings) with
    layers := 2, width := 2, queryHeads := 1, keyValueHeads := 1, headDim := 2, hidden := 2,
    expertHidden := 2, experts := 1 }

/-- The tables of the small weights: only the SiLU table is read. -/
private def smallTables : Tables :=
  { (default : Tables) with silu := { lowestKey := -1, entries := #[2, 2, 2] } }

/-- The matrix with the rows (30, 0) and (0, 40). -/
private def smallMatrix : Matrix := #[#[30, 0], #[0, 40]]

/-- The small weights. -/
private def smallWeights : Weights :=
  let block : GatedWeights :=
    { (default : GatedWeights) with up := smallMatrix, down := smallMatrix }
  let layer : LayerWeights :=
    { (default : LayerWeights) with
      value := smallMatrix, output := smallMatrix, shared := block, routed := #[block] }
  { (default : Weights) with perLayer := #[layer, layer] }

/-- No level for any matrix. -/
private def noLeastBoundLevels : LeastBoundLevels :=
  ⟨fun _ => [], fun _ _ => [], fun _ => [], fun _ => [], fun _ => [], fun _ _ => [], fun _ _ => [],
    fun _ _ => []⟩

example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 43, fun _ => 43, fun _ => 86, fun _ => 43, fun _ _ => 43,
      fun _ _ => 86, fun _ _ => 43⟩
    noLeastBoundLevels = true := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 42, fun _ _ => 43, fun _ => 43, fun _ => 86, fun _ => 43, fun _ _ => 43,
      fun _ _ => 86, fun _ _ => 43⟩
    noLeastBoundLevels = false := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 42, fun _ => 43, fun _ => 86, fun _ => 43, fun _ _ => 43,
      fun _ _ => 86, fun _ _ => 43⟩
    noLeastBoundLevels = false := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 43, fun _ => 42, fun _ => 86, fun _ => 43, fun _ _ => 43,
      fun _ _ => 86, fun _ _ => 43⟩
    noLeastBoundLevels = false := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 43, fun _ => 43, fun _ => 85, fun _ => 43, fun _ _ => 43,
      fun _ _ => 86, fun _ _ => 43⟩
    noLeastBoundLevels = false := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 43, fun _ => 43, fun _ => 86, fun _ => 42, fun _ _ => 43,
      fun _ _ => 86, fun _ _ => 43⟩
    noLeastBoundLevels = false := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 43, fun _ => 43, fun _ => 86, fun _ => 43, fun _ _ => 42,
      fun _ _ => 86, fun _ _ => 43⟩
    noLeastBoundLevels = false := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 43, fun _ => 43, fun _ => 86, fun _ => 43, fun _ _ => 43,
      fun _ _ => 85, fun _ _ => 43⟩
    noLeastBoundLevels = false := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 43, fun _ => 43, fun _ => 86, fun _ => 43, fun _ _ => 43,
      fun _ _ => 86, fun _ _ => 42⟩
    noLeastBoundLevels = false := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 43, fun _ => 43, fun _ => 43, fun _ => 43, fun _ _ => 43,
      fun _ _ => 86, fun _ _ => 43⟩
    noLeastBoundLevels = false := by decide +kernel
example : leastBoundNumbersPassScaledGramTest smallSettings smallTables smallWeights
    ⟨[], fun _ => 43, fun _ _ => 43, fun _ => 43, fun _ => 86, fun _ => 43, fun _ _ => 43,
      fun _ _ => 43, fun _ _ => 43⟩
    noLeastBoundLevels = false := by decide +kernel

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.hold_of_leastBoundNumbersPassScaledGramTest
#print axioms IntegerTransformer.Bounds.allConditionsHold_of_leastBoundNumbersPassScaledGramTest
