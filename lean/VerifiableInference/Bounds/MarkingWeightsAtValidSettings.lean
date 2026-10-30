-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/MarkingWeightsAtValidSettings.lean

The made-up weights `markingWeights`
(VerifiableInference/Bounds/PassingWeightsTellPromptsApart.lean) at every valid settings. In them
the first layer's attention block takes the mean of two values, so that the answer after two tokens
can depend on the first. That file has them at its example settings.

* `weightsAreValid_markingWeights_of_settingsAreValid`, `markingWeightsAt`: they are valid weights
  at every valid settings.
* `markingWeightsAt_small`: every matrix of every layer has every entry in -200 .. 200.
* `modelNextToken_markingWeightsAt_eq`: where no range condition ever fails at them, the model's
  next token after two tokens is the greedy choice at a row with one entry, `markedEntry`.
* `modelNextToken_markingWeightsAt_apart`: so, if the final norm's result at that entry is positive
  after the tokens 0, 1 and is 0 after the tokens 1, 1, the model answers these two prompts, which
  end in the same token, with 1 and with 0.

Limits. The weights are made up. The two conditions on the final norm are hypotheses here: whether
they hold depends on the settings' shifts. One attention layer takes a plain mean; the statement is
on two prompts of two tokens; no feed-forward block, router, rotary step or score takes part.
-/
import VerifiableInference.Bounds.PassingWeightsTellPromptsApart
import VerifiableInference.Bounds.SomeWeightsPassAtValidSettings

set_option autoImplicit false

namespace VerifiableInference.Bounds

open IntegerTransformer IntegerTransformer.Bounds

/-- The marking weights fit every valid settings and the system's tables. -/
theorem wellFormed_markingWeights_of_settingsAreValid (settings : Settings)
    (valid : settingsAreValid settings = true) :
    wellFormed settings lookupTables (markingWeights settings) = true := by
  obtain ⟨⟨positions, layers, _, queryHeads, keyValueHeads, headDim, hidden, expertHidden, _,
    vocabulary, _⟩, final, inRange, size⟩ := settingsAreValid_spec settings valid
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := lookupTables_wellFormed
  obtain ⟨d1, d2, e2⟩ := markingWeights_sizes settings
  obtain ⟨finalEps, _, _, _, finalShift, _⟩ := normInRange_spec _ _ _ final
  simp only [wellFormed, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by rw [queryHeads, keyValueHeads]⟩, by omega⟩,
    by omega⟩, by omega⟩, Or.inr (by omega)⟩, finalEps⟩, by omega⟩,
    by rw [positions, headDim]; exact c1⟩, by rw [positions, headDim]; exact c2⟩, c3⟩, c4⟩, c5⟩,
    c6⟩, c7⟩, d1⟩, d2⟩, size⟩, e2⟩, fun layer inLayers => ?_⟩
  obtain ⟨norm1, norm2, ⟨query, key, valueShift, output, gate, up, down⟩, routed⟩ :=
    layerSettingsInRange_spec _ _ (inRange layer (by omega))
  obtain ⟨eps1, _, _, _, shift1, _⟩ := normInRange_spec _ _ _ norm1
  obtain ⟨eps2, _, _, _, shift2, _⟩ := normInRange_spec _ _ _ norm2
  by_cases first : layer = 0
  · subst first
    rw [markingWeights_first _ inLayers, isMixture_zero]
    exact layerWellFormed_markingLayer settings _ eps1 eps2 (by omega) query key valueShift output
      (by omega) gate up down
  · rw [markingWeights_layer _ layer (by omega) inLayers]
    exact layerWellFormed_constantLayer settings _ 0 _ eps1 eps2 (by omega) query key valueShift
      output (by omega) gate up down routed

/-- The marking weights are valid at every valid settings. -/
theorem weightsAreValid_markingWeights_of_settingsAreValid (settings : Settings)
    (valid : settingsAreValid settings = true) :
    weightsAreValid settings (markingWeights settings) = true := by
  have layers := (settingsAreValid_spec settings valid).1.2.1
  simp only [weightsAreValid, weightsInRange, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨wellFormed_markingWeights_of_settingsAreValid settings valid,
    markingWeights_entries settings _ _ (by omega) (by omega) _ _ (by omega) (by omega),
    fun layer inLayers => ?_⟩
  by_cases first : layer = 0
  · subst first
    rw [markingWeights_first _ (by omega), isMixture_zero]
    exact layerWeightsInRange_markingLayer _
  · rw [markingWeights_layer _ layer (by omega) (by omega)]
    exact layerWeightsInRange_constantLayer _ _ _ (by decide) (by decide)

/-- The marking weights, at valid settings. -/
def markingWeightsAt (settings : Settings) (valid : settingsAreValid settings = true) :
    ModelWeights settings :=
  ⟨markingWeights settings, weightsAreValid_markingWeights_of_settingsAreValid settings valid⟩

/-- Every matrix of every layer of the marking weights has every entry in -200 .. 200. -/
theorem markingWeightsAt_small (settings : Settings) (valid : settingsAreValid settings = true)
    (layer : Nat) (inLayers : layer < settings.layers) :
    LayerWithin 200 ((markingWeightsAt settings valid).val.perLayer.entry layer) := by
  show LayerWithin 200 ((markingWeights settings).perLayer.entry layer)
  by_cases first : layer = 0
  · subst first
    rw [markingWeights_first _ inLayers]
    exact layerWithin_markingLayer _
  · rw [markingWeights_layer _ layer (by omega) inLayers]
    exact layerWithin_constantLayer _ _ _ _ (by decide)

/-- Where no range condition ever fails at the marking weights, the model's next token after two
tokens is the greedy choice at a row with one entry. -/
theorem modelNextToken_markingWeightsAt_eq (settings : Settings)
    (valid : settingsAreValid settings = true)
    (never : RangeConditionsNeverFail settings (markingWeightsAt settings valid))
    (first last : Nat) (firstToken : first < settings.vocabulary)
    (lastToken : last < settings.vocabulary) :
    modelNextToken settings (markingWeightsAt settings valid) [first, last] =
      some (firstArgmax (fun v => (product (rmsNorm settings.finalBits settings.finalShift
        settings.finalEps (rowWithOneEntry settings.width 0 (markedEntry settings first last))).out
        (countingWeights settings).head settings.vocabulary).entry v) settings.vocabulary) := by
  obtain ⟨⟨_, layers, width, queryHeads, keyValueHeads, _, _, _, _, _, _⟩, _, inRange, _⟩ :=
    settingsAreValid_spec settings valid
  obtain ⟨_, _, table, positive, _⟩ := lookupTables_wellFormed
  obtain ⟨next, isNext, _⟩ := modelNextToken_isSome_of_rangeConditionsNeverFail settings
    (markingWeightsAt settings valid) never [first, last] (by show 0 < 2; omega)
    (by show 2 ≤ 1024; omega) (by
      intro token inList
      rcases List.mem_cons.mp inList with isFirst | rest
      · rw [isFirst]; exact firstToken
      · rw [List.mem_singleton.mp rest]; exact lastToken)
  rw [isNext]
  obtain ⟨_, _, _, value⟩ := (model_eq_some _ _ _ _ _).mp isNext
  have spec := fun (layer : Nat) (inLayers : layer < settings.layers) =>
    layerSettingsInRange_spec _ _ (inRange layer (by omega))
  have choice := choice_markingWeights settings lookupTables first last firstToken lastToken
    (by omega) (by omega)
    (fun layer inLayers =>
      ⟨(spec layer inLayers).2.2.1.2.2.2.1, (spec layer inLayers).2.2.1.2.2.2.2.2.2⟩)
    (Nat.le_trans (by decide) (normInRange_spec _ _ _ (spec 0 (by omega)).1).2.2.2.2.1)
    (spec 0 (by omega)).2.2.1.1
    (by rw [queryHeads, keyValueHeads]) table positive
  exact congrArg some (value.symm.trans choice)

/-- **An earlier token matters**, if the mark survives the settings' shifts: the prompts `[0, 1]`
and `[1, 1]` end in the same token, and the model answers with 1 and with 0. -/
theorem modelNextToken_markingWeightsAt_apart (settings : Settings)
    (valid : settingsAreValid settings = true)
    (never : RangeConditionsNeverFail settings (markingWeightsAt settings valid))
    (marked : 0 < normOfOneEntry settings.finalBits settings.finalShift settings.finalEps
      (markedEntry settings 0 1))
    (unmarked : normOfOneEntry settings.finalBits settings.finalShift settings.finalEps
      (markedEntry settings 1 1) = 0) :
    modelNextToken settings (markingWeightsAt settings valid) [0, 1] = some 1 ∧
      modelNextToken settings (markingWeightsAt settings valid) [1, 1] = some 0 := by
  obtain ⟨⟨_, _, width, _, _, _, _, _, _, vocabulary, _⟩, final, _, _⟩ :=
    settingsAreValid_spec settings valid
  have finalShift : 1 ≤ settings.finalShift :=
    Nat.le_trans (by decide) (normInRange_spec _ _ _ final).2.2.2.2.1
  constructor
  · rw [modelNextToken_markingWeightsAt_eq settings valid never 0 1 (by omega) (by omega),
      choice_of_positive_entry settings _ (by omega) finalShift (by omega) marked]
  · rw [modelNextToken_markingWeightsAt_eq settings valid never 1 1 (by omega) (by omega),
      choice_of_zero_entry settings _ (by omega) finalShift (by omega) unmarked]

end VerifiableInference.Bounds

#print axioms VerifiableInference.Bounds.weightsAreValid_markingWeights_of_settingsAreValid
#print axioms VerifiableInference.Bounds.markingWeightsAt_small
#print axioms VerifiableInference.Bounds.modelNextToken_markingWeightsAt_apart
