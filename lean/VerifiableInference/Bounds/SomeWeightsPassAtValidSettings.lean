-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/SomeWeightsPassAtValidSettings.lean

At every valid settings some weights pass the worst-case check.
- `passesWorstCaseCheck_of_zero_layers`: at every settings that pass `settingsAreValid`, all weights
  pass whose layers' matrices are zero and whose embedding has every entry in `-2^25 .. 2^25`
  (2^25 = 33,554,432). Their head matrix (`weights.head`: from the last stream to the logits) is
  free, within `weightsAreValid`.
- `zeroModelWeights`: the weights with 0 at every place, valid at every valid settings; they pass
  (`passesWorstCaseCheck_zeroModelWeights`).
- `exists_passesWorstCaseCheck`: so at every valid settings there are weights that pass.
The proof reads no number of any settings: it uses the ranges that `settingsAreValid` asks for. With
zero layers every product and every addition is 0, so the stream is a row of the embedding, and the
two tests at a norm follow from `normInRange`.
Limits: layers of zeros compute nothing: at such weights the next token depends on the last token
alone. The theorems say that the check's premise can be met at every valid settings, no more. 2^25
is the largest power of two at which the uniform test passes at all valid settings: at 2^26 it
refuses at a norm with the exponents 31 and 17, which are in range. The file imports Lean's core and
the model's own files.
-/
import VerifiableInference.Bounds.SomeWeightsPass

set_option autoImplicit false

namespace VerifiableInference.Bounds

open IntegerTransformer IntegerTransformer.Bounds

/-! ## 1. The parts of the tests on the settings, as statements -/

/-- The parts of `normInRange`. -/
theorem normInRange_spec (bits shift : Nat) (eps : Int) (h : normInRange bits shift eps = true) :
    1 ≤ eps ∧ eps < 2 ^ 48 ∧ 24 ≤ bits ∧ bits ≤ 47 ∧ 17 ≤ shift ∧ shift ≤ 32 ∧
      bits ≤ shift + 14 ∧ shift ≤ bits := by
  simp only [normInRange, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, i⟩

/-- Of `layerSettingsInRange`: the two norms are in range, and every shift that the layer hands to
`roundShift` is at least 1. -/
theorem layerSettingsInRange_spec (mixture : Bool) (p : LayerSettings)
    (h : layerSettingsInRange mixture p = true) :
    normInRange p.attentionBits p.attentionShift p.attentionEps = true ∧
    normInRange p.feedForwardBits p.feedForwardShift p.feedForwardEps = true ∧
    (1 ≤ p.queryShift ∧ 1 ≤ p.keyShift ∧ 1 ≤ p.valueShift ∧ 1 ≤ p.outputShift ∧ 1 ≤ p.gateShift ∧
      1 ≤ p.upShift ∧ 1 ≤ p.downShift) ∧
    (mixture = true → 1 ≤ p.routerShift ∧ 1 ≤ p.routedGateShift ∧ 1 ≤ p.routedUpShift) := by
  simp only [layerSettingsInRange, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨q1, q2⟩, k1⟩, k2⟩, qk⟩, v1⟩, v2⟩, o1⟩, o2⟩, g1⟩, g2⟩, u1⟩, u2⟩,
    d1⟩, d2⟩, s1⟩, s2⟩, n1⟩, n2⟩, rest⟩ := h
  refine ⟨n1, n2, ⟨by omega, by omega, v1, o1, g1, u1, by omega⟩, fun mix => ?_⟩
  simp only [mix, if_true, Bool.and_eq_true, decide_eq_true_eq] at rest
  omega

/-- The parts of `settingsAreValid` that are used below. -/
theorem settingsAreValid_spec (settings : Settings) (valid : settingsAreValid settings = true) :
    (settings.positions = 1024 ∧ settings.layers = 48 ∧ settings.width = 5120 ∧
      settings.queryHeads = 40 ∧ settings.keyValueHeads = 8 ∧ settings.headDim = 128 ∧
      settings.hidden = 16384 ∧ settings.expertHidden = 8192 ∧ settings.experts = 128 ∧
      settings.vocabulary = 202048 ∧ settings.rotaryScale = 12) ∧
    normInRange settings.finalBits settings.finalShift settings.finalEps = true ∧
    (∀ l, l < 48 →
      layerSettingsInRange (settings.isMixture l) (settings.perLayer.entry l) = true) ∧
    settings.perLayer.size = settings.layers := by
  simp only [settingsAreValid, hasModelSizes, settingsInRange, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, List.mem_range] at valid
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h⟩, i⟩, j⟩, k⟩, _⟩, final, layers⟩, size⟩ := valid
  exact ⟨⟨a, b, c, d, e, f, g, h, i, j, k⟩, final, fun l hl => (layers l hl).1, size⟩

/-! ## 2. At valid settings the uniform test passes for zero layers -/

/-- For `k ≥ 1`, `roundShift 0 k` is 0. -/
theorem roundShift_zero (k : Nat) (h : 1 ≤ k) : roundShift 0 k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have positive : (0 : Int) < 2 ^ j := Int.pow_pos (by decide)
  unfold roundShift
  rw [Int.zero_add, Nat.add_sub_cancel, Int.pow_succ]
  exact Int.ediv_eq_zero_of_lt (by omega) (by omega)

/-- A column of zeros has the uniform bound 0. -/
theorem uniformColumnBound_zero (inputBound : Int) (rows : Nat) :
    uniformColumnBound inputBound rows 0 = 0 := by
  simp [uniformColumnBound]

/-- The norm's second test, at all exponents that `normInRange` admits, for a root of at most
`3 * 2^30`. -/
theorem quotient_fits_at_all_exponents : ∀ bits, bits < 48 → ∀ shift, shift < 33 → 17 ≤ shift →
    bits ≤ shift + 14 → roundShift (2 ^ bits + 3 * 2 ^ 29) shift ≤ 32767 := by
  decide +kernel

/-! At `2^26` the test refuses at exponents that are in range. -/
example : normInRange 31 17 1 = true ∧ uniformNormFits 31 17 1 5120 67108864 = false := by
  decide +kernel

/-- A norm in range passes `uniformNormFits` at 5,120 coordinates within `2^25`. -/
theorem uniformNormFits_of_normInRange (bits shift : Nat) (eps : Int)
    (h : normInRange bits shift eps = true) :
    uniformNormFits bits shift eps 5120 33554432 = true := by
  obtain ⟨_, eps_small, _, bits_small, shift_large, shift_small, near, _⟩ :=
    normInRange_spec bits shift eps h
  have squares : ((5120 : Nat) : Int) * (33554432 * 33554432) = 5764607523034234880 := by decide
  have power48 : (2 : Int) ^ 48 = 281474976710656 := by decide
  have power78 : (2 : Int) ^ 78 = 302231454903657293676544 := by decide
  have root := isqrt_le_of_lt_square (((5120 : Nat) : Int) * (33554432 * 33554432) + eps).toNat
    (3 * 2 ^ 30) (by
      have : (3 * 2 ^ 30 + 1) * (3 * 2 ^ 30 + 1) = 10376293547904073729 := by decide
      omega)
  have half : (3 : Int) * 2 ^ 29 = 1610612736 := by decide
  have whole : ((3 * 2 ^ 30 : Nat) : Int) = 3221225472 := by decide
  simp only [uniformNormFits, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, Int.le_trans (roundShift_le_roundShift _ (2 ^ bits + 3 * 2 ^ 29) _ (by omega))
    (quotient_fits_at_all_exponents bits (by omega) shift (by omega) shift_large near)⟩

/-- What one layer adds has the uniform bound 0, if its matrices are zero. -/
theorem uniformLayerAddition_zero (settings : Settings) (silu : Int) (l : Nat)
    (inRange : layerSettingsInRange (settings.isMixture l) (settings.perLayer.entry l) = true) :
    uniformLayerAddition settings silu 0 l = 0 := by
  obtain ⟨_, _, ⟨_, _, _, output, _, _, down⟩, _⟩ := layerSettingsInRange_spec _ _ inRange
  unfold uniformLayerAddition uniformAttentionAddition uniformFeedForwardAddition uniformDownBound
  simp only [uniformColumnBound_zero, Int.add_zero, ite_self, roundShift_zero _ output,
    roundShift_zero _ down]

/-- So the stream's uniform bound is the embedding's, up to the last layer. -/
theorem uniformStreamBound_zero (settings : Settings) (silu embedding : Int) (l : Nat)
    (hl : l ≤ 48)
    (inRange : ∀ l, l < 48 →
      layerSettingsInRange (settings.isMixture l) (settings.perLayer.entry l) = true) :
    uniformStreamBound settings silu 0 embedding l = embedding := by
  have zeros : sumOver l (fun below => uniformLayerAddition settings silu 0 below) =
      sumOver l fun _ => 0 :=
    sumOver_congr l _ _ fun below h =>
      uniformLayerAddition_zero settings silu below (inRange below (by omega))
  unfold uniformStreamBound
  rw [zeros, sumOver_const]
  omega

/-- **At valid settings `uniformCheck` passes for layers whose matrices are zero and an embedding
within `2^25`.** -/
theorem uniformCheck_zero_of_settingsAreValid (settings : Settings)
    (valid : settingsAreValid settings = true) :
    uniformCheck settings 4096 4095 0 33554432 = true := by
  obtain ⟨⟨_, layers, width, _, _, _, _, _, _, _, scale⟩, final, inRange, _⟩ :=
    settingsAreValid_spec settings valid
  simp only [uniformCheck, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨by decide, by decide⟩, by decide⟩, by rw [scale]; decide⟩, fun l hl => ?_⟩, ?_⟩
  · rw [layers] at hl
    obtain ⟨norm1, norm2, ⟨query, key, value, output, gate, up, _⟩, routed⟩ :=
      layerSettingsInRange_spec _ _ (inRange l hl)
    simp only [uniformLayerFits, uniformUnitsFit, uniformUpBound, uniformAttentionAddition,
      uniformColumnBound_zero, Int.mul_zero, Int.add_zero, Bool.and_eq_true, decide_eq_true_eq,
      Bool.or_eq_true, Bool.not_eq_true', roundShift_zero _ query, roundShift_zero _ key,
      roundShift_zero _ value, roundShift_zero _ output, roundShift_zero _ gate,
      roundShift_zero _ up, uniformStreamBound_zero settings 4095 33554432 l (by omega) inRange,
      width]
    refine ⟨⟨⟨⟨⟨⟨uniformNormFits_of_normInRange _ _ _ norm1, by decide⟩, by decide⟩, by decide⟩,
      uniformNormFits_of_normInRange _ _ _ norm2⟩, by decide, by decide⟩, ?_⟩
    cases mix : settings.isMixture l with
    | false => exact Or.inl rfl
    | true =>
      obtain ⟨router, routedGate, routedUp⟩ := routed mix
      rw [roundShift_zero _ router, roundShift_zero _ routedGate, roundShift_zero _ routedUp]
      exact Or.inr ⟨by decide, by decide, by decide⟩
  · rw [layers, uniformStreamBound_zero settings 4095 33554432 48 (by omega) inRange, width]
    exact uniformNormFits_of_normInRange _ _ _ final

/-! ## 3. All weights with zero layers pass, at every valid settings -/

/-- **At every valid settings all weights pass whose layers' matrices are zero and whose embedding
has every entry in `-2^25 .. 2^25`**, whatever their head matrix is. -/
theorem passesWorstCaseCheck_of_zero_layers (settings : Settings)
    (valid : settingsAreValid settings = true) (weights : ModelWeights settings)
    (zero : ∀ l, l < settings.layers → LayerWithin 0 (weights.val.perLayer.entry l))
    (embedding : MatrixWithin 33554432 weights.val.embedding) :
    PassesWorstCaseCheck settings weights :=
  boxWorstCaseCheck_of_uniformCheck settings lookupTables weights.val 4096 4095 0 33554432
    cosineTable_within sineTable_within siluTable_within routedInputFits_lookupTables embedding zero
    (uniformCheck_zero_of_settingsAreValid settings valid)

/-! ## 4. At every valid settings there are such weights -/

/-- The constant weights fit every valid settings and the system's tables. -/
theorem wellFormed_constantWeights_of_settingsAreValid (settings : Settings)
    (valid : settingsAreValid settings = true) (value : Int) :
    wellFormed settings lookupTables (constantWeights settings value) = true := by
  obtain ⟨⟨positions, layers, _, queryHeads, keyValueHeads, headDim, hidden, expertHidden, _,
    vocabulary, _⟩, final, inRange, size⟩ := settingsAreValid_spec settings valid
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := lookupTables_wellFormed
  obtain ⟨d1, d2, e2⟩ := constantWeights_sizes settings value
  obtain ⟨finalEps, _, _, _, finalShift, _⟩ := normInRange_spec _ _ _ final
  simp only [wellFormed, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by rw [queryHeads, keyValueHeads]⟩, by omega⟩,
    by omega⟩, by omega⟩, Or.inr (by omega)⟩, finalEps⟩, by omega⟩,
    by rw [positions, headDim]; exact c1⟩, by rw [positions, headDim]; exact c2⟩, c3⟩, c4⟩, c5⟩,
    c6⟩, c7⟩, d1⟩, d2⟩, size⟩, e2⟩, fun l hl => ?_⟩
  rw [constantWeights_layer _ _ l hl]
  obtain ⟨norm1, norm2, ⟨query, key, valueShift, output, gate, up, down⟩, routed⟩ :=
    layerSettingsInRange_spec _ _ (inRange l (by omega))
  obtain ⟨eps1, _, _, _, shift1, _⟩ := normInRange_spec _ _ _ norm1
  obtain ⟨eps2, _, _, _, shift2, _⟩ := normInRange_spec _ _ _ norm2
  exact layerWellFormed_constantLayer settings _ value _ eps1 eps2 (by omega) query key valueShift
    output (by omega) gate up down routed

/-- The constant weights are valid at every valid settings, if their number has 13 bits. -/
theorem weightsAreValid_constantWeights_of_settingsAreValid (settings : Settings)
    (valid : settingsAreValid settings = true) (value : Int) (lower : -4096 ≤ value)
    (upper : value ≤ 4095) : weightsAreValid settings (constantWeights settings value) = true := by
  have layers := (settingsAreValid_spec settings valid).1.2.1
  simp only [weightsAreValid, weightsInRange, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨wellFormed_constantWeights_of_settingsAreValid settings valid value,
    ⟨(constantWeights_entries settings value _ _ (by omega) (by omega)).1,
      (constantWeights_entries settings value _ _ lower upper).2⟩, fun l hl => ?_⟩
  rw [constantWeights_layer _ _ l (by omega)]
  exact layerWeightsInRange_constantLayer _ _ _ lower upper

/-- The weights with 0 at every place of every matrix, at valid settings. -/
def zeroModelWeights (settings : Settings) (valid : settingsAreValid settings = true) :
    ModelWeights settings :=
  ⟨constantWeights settings 0,
    weightsAreValid_constantWeights_of_settingsAreValid settings valid 0 (by decide) (by decide)⟩

/-- The zero weights pass, at every valid settings. -/
theorem passesWorstCaseCheck_zeroModelWeights (settings : Settings)
    (valid : settingsAreValid settings = true) :
    PassesWorstCaseCheck settings (zeroModelWeights settings valid) := by
  apply passesWorstCaseCheck_of_zero_layers settings valid
  · intro l hl
    show LayerWithin 0 ((constantWeights settings 0).perLayer.entry l)
    rw [constantWeights_layer _ _ l hl]
    exact layerWithin_constantLayer _ _ _ _ (by decide)
  · exact matrixWithin_constantMatrix _ _ _ _ (by decide)

/-- **At every valid settings some weights pass the worst-case check.** -/
theorem exists_passesWorstCaseCheck (settings : Settings)
    (valid : settingsAreValid settings = true) :
    ∃ weights : ModelWeights settings, PassesWorstCaseCheck settings weights :=
  ⟨zeroModelWeights settings valid, passesWorstCaseCheck_zeroModelWeights settings valid⟩

end VerifiableInference.Bounds

#print axioms VerifiableInference.Bounds.uniformCheck_zero_of_settingsAreValid
#print axioms VerifiableInference.Bounds.passesWorstCaseCheck_of_zero_layers
#print axioms VerifiableInference.Bounds.exists_passesWorstCaseCheck
