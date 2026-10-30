-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/PassingWeightsTellPromptsApart.lean

Among the weights that pass the worst-case check there are weights at which the model's answer
depends on the prompt: on its last token, and on an earlier one. Two made-up members of the family
of `passesWorstCaseCheck_of_small_entries`, at `exampleSettings`
(VerifiableInference/Bounds/SomeWeightsPass.lean).

`countingModelWeights`. All matrices of all layers are zero. The embedding sends token `t` to the
row with 1,000 at place `t % 5120` and 0 elsewhere. The head matrix (`weights.head`: from the last
stream to the logits) has 1 at row `k`, column `k + 1`, and 0 elsewhere.
- `passesWorstCaseCheck_countingModelWeights`: they pass.
- `modelNextToken_countingModelWeights`: after 1 to 1,024 tokens of the vocabulary, the last of them
  `last`, the model's next token is `last % 5120 + 1`.
- `modelNextToken_countingModelWeights_apart`: so it answers the prompts `[0]` and `[1]`
  differently, with 1 and with 2.
- `greedyOutput_countingModelWeights`: after the prompt `[5]` the output 6, 7, 8 is the model's own,
  token by token.

`markingModelWeights`. The embedding sends token 0 to the row with 1,000 at place 0, and every other
token to the zero row. In the first layer the value matrix has 200 at every place and the layer's
output matrix has 200 in column 0. All other matrices of all layers are zero. The head matrix is as
above. The 200 is no figure of the example: `markingWeights` is defined at all settings.
- `passesWorstCaseCheck_markingModelWeights`: they pass.
- `modelNextToken_markingModelWeights_apart`: the prompts `[0, 1]` and `[1, 1]` end in the same
  token, and the model answers with 1 and with 0.

How it is proved. A layer adds nothing to the stream if the layer's output matrix and its down
matrices are zero (`layer_out_of_zero`), at any settings with shifts of at least 1. The norm of a
row with one entry that is not zero has one such entry, at the same place (`rmsNorm_oneEntry`), so
at most one logit is not 0. With a zero query matrix all scores are 0, so an attention head returns
the rounded mean of the values (`attendHead_out_of_zero_queries`, at the second of two positions);
after `[0, 1]` the values are 3 and 0, their mean rounds to 2, and the first layer adds 4 at place
0 of the second row; after `[1, 1]` it adds 0 (`markedEntry_exampleSettings` and the example after
it). The range conditions come from the check, not from a computation.

Limits: the weights are made up. Three places of the settings have the reference table's number
(SomeWeightsPass.lean, part 2), and the settings may depend on Llama 2 7B and Llama 4 Maverick as
far as those three places do: the value shift is fixed by a test that stood while the example still
had the reference table's shifts (THIRD_PARTY.md). At the first weights the layers do nothing; at
the second one attention layer takes a plain mean, on two prompts of two tokens; no feed-forward
block, router, rotary step or score takes part. A few numbers are evaluated in Lean's kernel
(`decide +kernel`). The file imports Lean's core and the model's own files.
-/
import VerifiableInference.Bounds.SomeWeightsPass
import VerifiableInference.GreedyOutputExists

set_option autoImplicit false

namespace VerifiableInference.Bounds

open IntegerTransformer IntegerTransformer.Bounds

/-! ## 1. Arithmetic and arrays -/

/-- A sum of terms that are all 0 is 0. -/
private theorem sumOver_of_terms_zero (n : Nat) (f : Nat → Int) (h : ∀ k, k < n → f k = 0) :
    sumOver n f = 0 := by
  induction n with
  | zero => rfl
  | succ n step =>
    simp only [sumOver]
    rw [step (fun k inside => h k (by omega)), h n (by omega)]
    rfl

/-- A sum with one term that may differ from 0 is that term. -/
private theorem sumOver_of_one_term (n place : Nat) (f : Nat → Int) (inside : place < n)
    (h : ∀ k, k < n → k ≠ place → f k = 0) : sumOver n f = f place := by
  induction n with
  | zero => omega
  | succ n step =>
    simp only [sumOver]
    by_cases last : place = n
    · subst last
      rw [sumOver_of_terms_zero place f fun k below => h k (by omega) (by omega), Int.zero_add]
    · rw [step (by omega) fun k below => h k (by omega), h n (by omega) (by omega), Int.add_zero]

/-- 0, shifted by at least one place, is 0. -/
private theorem roundShift_of_zero (shift : Nat) (positive : 1 ≤ shift) :
    roundShift 0 shift = 0 := by
  obtain ⟨less, rfl⟩ : ∃ less, shift = less + 1 := ⟨shift - 1, by omega⟩
  have power : (0 : Int) < 2 ^ less := Int.pow_pos (by decide)
  unfold roundShift
  rw [Nat.add_sub_cancel, Int.pow_succ]
  exact Int.ediv_eq_zero_of_lt (by omega) (by omega)

/-- The array of an array's reads is the array. -/
theorem tabulate_reads {α : Type} [Inhabited α] (v : Array α) :
    (tabulate v.size fun k => v.entry k) = v := by
  apply Array.ext (size_tabulate _ _)
  intro i inTable inArray
  rw [← entry_inside _ i inTable, ← entry_inside _ i inArray, tabulate_read _ _ _ inArray]

/-- Adding a vector whose reads are all 0 changes nothing. -/
theorem addVec_of_reads_zero (x y : IntegerVector) (h : ∀ k, y.entry k = 0) : addVectors x y = x := by
  unfold addVectors
  have same : (fun k => x.entry k + y.entry k) = fun k => x.entry k :=
    funext fun k => by rw [h k, Int.add_zero]
  rw [same, tabulate_reads]

/-- Every read of a matrix within 0 is 0. -/
theorem read_of_matrixWithin_zero (W : Matrix) (zero : MatrixWithin 0 W) (k j : Nat) :
    (W.entry k).entry j = 0 := by
  have bound := zero k j
  rw [magnitude_le_iff] at bound
  omega

/-- If `f` is positive at one index below `n` and 0 at the others, that index is the argmax. -/
theorem firstArgmax_of_one_positive (f : Nat → Int) (n place : Nat) (inside : place < n)
    (positive : 0 < f place) (h : ∀ v, v < n → v ≠ place → f v = 0) :
    firstArgmax f n = place := by
  obtain ⟨below, largest, _⟩ := firstArgmax_spec f n (by omega)
  apply Classical.byContradiction
  intro other
  have zero := h _ below other
  have least := largest place inside
  omega

/-! ## 2. A layer adds nothing if the layer's output matrix and its down matrices are zero -/

/-- What attention adds, if the layer's output matrix is zero: every read is 0. -/
theorem attention_addition_of_zero (mixed : Matrix) (W : Matrix) (width shift : Nat)
    (zero : MatrixWithin 0 W) (positive : 1 ≤ shift) (t k : Nat) :
    ((mixed.map fun o => (product o W width).map fun e => roundShift e shift).entry t).entry k =
      0 := by
  by_cases position : t < mixed.size
  · rw [map_read _ _ _ position]
    by_cases place : k < width
    · rw [map_read _ _ _ (by rw [size_product]; exact place)]
      unfold product
      rw [tabulate_read _ _ _ place, sumOver_of_terms_zero _ _ fun j _ => by
        rw [read_of_matrixWithin_zero W zero, Int.mul_zero]]
      exact roundShift_of_zero shift positive
    · rw [entry_outside _ k (by rw [Array.size_map, size_product]; exact place)]
      rfl
  · rw [entry_outside _ t (by rw [Array.size_map]; exact position)]
    rfl

/-- Attention leaves the stream as it is, if the layer's output matrix is zero. -/
theorem attention_out_of_zero (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix) (zero : MatrixWithin 0 w.output)
    (positive : 1 ≤ p.outputShift) : (attention s p tables w x).out = x := by
  simp only [attention]
  have same : ∀ added : Matrix, (∀ t k, (added.entry t).entry k = 0) →
      (tabulate x.size fun t => addVectors (x.entry t) (added.entry t)) = x := by
    intro added reads
    have rows : (fun t => addVectors (x.entry t) (added.entry t)) = fun t => x.entry t :=
      funext fun t => addVec_of_reads_zero _ _ (reads t)
    rw [rows, tabulate_reads]
  exact same _ (attention_addition_of_zero _ w.output s.width p.outputShift zero positive)

/-- A down projection with a zero matrix is 0. -/
theorem downSum_of_zero (units : HiddenUnits) (down : Matrix) (zero : MatrixWithin 0 down)
    (k : Nat) : downSum units down k = 0 := by
  unfold downSum
  exact sumOver_of_terms_zero _ _ fun j _ => by
    rw [read_of_matrixWithin_zero down zero, Int.mul_zero]

/-- A vector that is given entry by entry, all 0, reads 0 everywhere. -/
private theorem read_tabulate_of_zero (n : Nat) (f : Nat → Int) (h : ∀ k, f k = 0) (k : Nat) :
    (tabulate n f).entry k = 0 := by
  by_cases inside : k < n
  · rw [tabulate_read _ _ _ inside, h k]
  · rw [entry_outside _ k (by rw [size_tabulate]; exact inside)]
    rfl

/-- The feed-forward block with zero down matrices leaves a row as it is. -/
theorem feedForward_out_of_zero (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (mixture : Bool) (x : IntegerVector) (shared : MatrixWithin 0 w.shared.down)
    (routed : ∀ e, MatrixWithin 0 (w.routed.entry e).down) (positive : 1 ≤ p.downShift) :
    (feedForward s p tables w mixture x).out = x := by
  cases mixture with
  | false =>
    simp only [feedForward, Bool.false_eq_true, if_false]
    exact addVec_of_reads_zero _ _ (read_tabulate_of_zero _ _ fun k => by
      rw [downSum_of_zero _ _ shared]; exact roundShift_of_zero _ positive)
  | true =>
    simp only [feedForward, if_true]
    exact addVec_of_reads_zero _ _ (read_tabulate_of_zero _ _ fun k => by
      rw [downSum_of_zero _ _ shared, downSum_of_zero _ _ (routed _)]
      exact roundShift_of_zero _ positive)

/-- **A layer leaves the stream as it is, if the layer's output matrix and its down matrices are
zero.** -/
theorem layer_out_of_zero (s : Settings) (tables : Tables) (weights : Weights) (l : Nat)
    (x : Matrix) (zero : LayerWithin 0 (weights.perLayer.entry l))
    (output : 1 ≤ (s.perLayer.entry l).outputShift) (down : 1 ≤ (s.perLayer.entry l).downShift) :
    (layer s tables weights l x).out = x := by
  simp only [layer]
  rw [attention_out_of_zero s _ tables _ x zero.2.2.2.1 output, Array.map_map]
  have same : ((fun ff : FeedForward => ff.out) ∘ fun row =>
      feedForward s (s.perLayer.entry l) tables (weights.perLayer.entry l) (s.isMixture l) row) =
      id :=
    funext fun row => feedForward_out_of_zero s _ tables _ _ row zero.2.2.2.2.1.2.2
      (fun e => (zero.2.2.2.2.2.2 e).2.2) down
  rw [same, Array.map_id]

/-- If all layers are such, the stream above any number of them is the embedded tokens. -/
theorem streamAbove_of_zero (s : Settings) (tables : Tables) (weights : Weights) (x0 : Matrix)
    (zero : ∀ l, l < s.layers → LayerWithin 0 (weights.perLayer.entry l))
    (shifts : ∀ l, l < s.layers →
      1 ≤ (s.perLayer.entry l).outputShift ∧ 1 ≤ (s.perLayer.entry l).downShift)
    (l : Nat) (inside : l ≤ s.layers) :
    streamAbove x0 (firstLayers s tables weights x0 l) = x0 := by
  induction l with
  | zero => exact streamAbove_zero s tables weights x0
  | succ l step =>
    rw [streamAbove_succ, step (by omega)]
    exact layer_out_of_zero s tables weights l x0 (zero l inside) (shifts l inside).1
      (shifts l inside).2

/-! ## 3. The norm of a row with one entry -/

/-- The row of `size` entries with `value` at `place` and 0 elsewhere. -/
def rowWithOneEntry (size place : Nat) (value : Int) : IntegerVector :=
  tabulate size fun k => if k = place then value else 0

/-- What a norm returns at the place of the one entry. -/
def normOfOneEntry (bits shift : Nat) (eps value : Int) : Int :=
  let root : Int := integerSquareRoot (value * value + eps).toNat
  clamp (roundShift (value * ((2 ^ bits + root / 2) / root)) shift) activationBound

/-- A norm's result on a row with one entry: one entry, at the same place. -/
theorem rmsNorm_oneEntry (bits shift : Nat) (eps : Int) (size place : Nat) (value : Int)
    (positive : 1 ≤ shift) (inside : place < size) (k : Nat) (below : k < size) :
    (rmsNorm bits shift eps (rowWithOneEntry size place value)).out.entry k =
      if k = place then normOfOneEntry bits shift eps value else 0 := by
  have sum : (sumOver (rowWithOneEntry size place value).size fun k =>
      (rowWithOneEntry size place value).entry k * (rowWithOneEntry size place value).entry k) =
      value * value := by
    unfold rowWithOneEntry
    rw [size_tabulate, sumOver_of_one_term size place _ inside fun k below other => by
      rw [tabulate_read _ _ _ below, if_neg other, Int.mul_zero],
      tabulate_read _ _ _ inside, if_pos rfl]
  simp only [rmsNorm, normOfOneEntry, sum]
  have size_row : (rowWithOneEntry size place value).size = size := size_tabulate _ _
  rw [map_read _ _ _ (by rw [Array.size_map, size_row]; exact below),
    map_read _ _ _ (by rw [size_row]; exact below)]
  unfold rowWithOneEntry
  rw [tabulate_read _ _ _ below]
  by_cases here : k = place
  · rw [if_pos here, if_pos here]
  · rw [if_neg here, if_neg here, Int.zero_mul, roundShift_of_zero shift positive]
    decide

/-! ## 4. The weights, at any settings -/

/-- Made-up weights. All matrices of all layers are zero; the embedding sends token `t` to the row
with 1,000 at place `t % d`; the head matrix has 1 at row `k`, column `k + 1`. -/
def countingWeights (s : Settings) : Weights where
  embedding := tabulate s.vocabulary fun token => tabulate s.width fun k =>
    if k = token % s.width then 1000 else 0
  perLayer := tabulate s.layers fun l => constantLayer s 0 (s.isMixture l)
  head := tabulate s.width fun k => tabulate s.vocabulary fun v => if v = k + 1 then 1 else 0

/-- The layers of these weights. -/
theorem countingWeights_layer (s : Settings) (l : Nat) (h : l < s.layers) :
    (countingWeights s).perLayer.entry l = constantLayer s 0 (s.isMixture l) := by
  simp only [countingWeights]
  rw [tabulate_read _ _ _ h]

/-- The layers of these weights are zero. -/
theorem layerWithin_countingWeights (s : Settings) (bound : Int) (nonneg : 0 ≤ bound) (l : Nat)
    (h : l < s.layers) : LayerWithin bound ((countingWeights s).perLayer.entry l) := by
  rw [countingWeights_layer s l h]
  exact layerWithin_constantLayer _ _ _ _ (by rw [magnitude_le_iff]; omega)

/-- The logits of these weights at a row with one entry: one logit, at the place plus 1. -/
theorem logit_countingWeights (s : Settings) (place : Nat) (value : Int)
    (inside : place < s.width) (positive : 1 ≤ s.finalShift) (v : Nat)
    (token : v < s.vocabulary) :
    (product (rmsNorm s.finalBits s.finalShift s.finalEps (rowWithOneEntry s.width place value)).out
      (countingWeights s).head s.vocabulary).entry v =
      if v = place + 1 then normOfOneEntry s.finalBits s.finalShift s.finalEps value else 0 := by
  have size : (rmsNorm s.finalBits s.finalShift s.finalEps
      (rowWithOneEntry s.width place value)).out.size = s.width := by
    rw [(size_rmsNorm _ _ _ _).2]; exact size_tabulate _ _
  unfold product
  rw [tabulate_read _ _ _ token, size, sumOver_of_one_term s.width place _ inside
    fun k below other => by
      rw [rmsNorm_oneEntry _ _ _ _ _ _ positive inside k below, if_neg other, Int.zero_mul],
    rmsNorm_oneEntry _ _ _ _ _ _ positive inside place inside, if_pos rfl]
  simp only [countingWeights]
  rw [tabulate_read _ _ _ inside, tabulate_read _ _ _ token]
  by_cases here : v = place + 1
  · rw [if_pos here, if_pos here, Int.mul_one]
  · rw [if_neg here, if_neg here, Int.mul_zero]

/-- **The greedy choice at these weights**, at the last position of a prompt: the last token's rest
on division by the width, plus 1. -/
theorem choice_countingWeights (s : Settings) (tables : Tables) (prompt : Array Nat)
    (prompt_ok : isPrompt s prompt = true)
    (shifts : ∀ l, l < s.layers →
      1 ≤ (s.perLayer.entry l).outputShift ∧ 1 ≤ (s.perLayer.entry l).downShift)
    (finalShift : 1 ≤ s.finalShift) (some_width : 0 < s.width) (wide : s.width < s.vocabulary)
    (positive : 0 < normOfOneEntry s.finalBits s.finalShift s.finalEps 1000) :
    (trace s tables (countingWeights s) prompt).choices.entry (prompt.size - 1) =
      prompt.entry (prompt.size - 1) % s.width + 1 := by
  obtain ⟨some_token, _, tokens⟩ := isPrompt_spec s prompt prompt_ok
  have last : prompt.size - 1 < prompt.size := by omega
  have place : prompt.entry (prompt.size - 1) % s.width < s.width := Nat.mod_lt _ some_width
  simp only [trace]
  rw [streamAbove_of_zero s tables (countingWeights s) _
    (layerWithin_countingWeights s 0 (Int.le_refl 0)) shifts s.layers (Nat.le_refl _),
    map_read _ _ _ (by simp only [Array.size_map]; exact last),
    map_read _ _ _ (by simp only [Array.size_map]; exact last),
    map_read _ _ _ (by simp only [Array.size_map]; exact last),
    map_read _ _ _ last]
  have row : (countingWeights s).embedding.entry (prompt.entry (prompt.size - 1)) =
      rowWithOneEntry s.width (prompt.entry (prompt.size - 1) % s.width) 1000 := by
    simp only [countingWeights]
    rw [tabulate_read _ _ _ (tokens _ last)]
    rfl
  rw [row]
  apply firstArgmax_of_one_positive _ _ _ (by omega)
  · rw [logit_countingWeights s _ 1000 place finalShift _ (by omega), if_pos rfl]
    exact positive
  · intro v token other
    rw [logit_countingWeights s _ 1000 place finalShift v token, if_neg other]

/-! ## 5. The weights at the example settings -/

/-- The entries of a matrix that is given entry by entry are in every interval that holds them
all. -/
theorem entriesWithin_tabulate (rows columns : Nat) (f : Nat → Nat → Int) (low high : Int)
    (h : ∀ k j, low ≤ f k j ∧ f k j ≤ high) :
    entriesWithin low high (tabulate rows fun k => tabulate columns fun j => f k j) = true := by
  unfold entriesWithin
  refine all_of_reads _ _ fun k row => all_of_reads _ _ fun j column => ?_
  rw [size_tabulate] at row
  rw [tabulate_read _ _ _ row, size_tabulate] at column
  rw [tabulate_read _ _ _ row, tabulate_read _ _ _ column]
  simp [(h k j).1, (h k j).2]

/-- The sizes of the embedding, of the head matrix and of the array of layers. -/
theorem countingWeights_sizes (s : Settings) :
    hasSize s.vocabulary s.width (countingWeights s).embedding = true ∧
    hasSize s.width s.vocabulary (countingWeights s).head = true ∧
    (countingWeights s).perLayer.size = s.layers :=
  ⟨hasSize_tabulate _ _ _, hasSize_tabulate _ _ _, size_tabulate _ _⟩

/-- The entries of the embedding are in 0 .. 1,000, and those of the head matrix in 0 .. 1. -/
theorem countingWeights_entries (s : Settings) (low high : Int) (lower : low ≤ 0)
    (upper : 1000 ≤ high) (low' high' : Int) (lower' : low' ≤ 0) (upper' : 1 ≤ high') :
    entriesWithin low high (countingWeights s).embedding = true ∧
    entriesWithin low' high' (countingWeights s).head = true :=
  ⟨entriesWithin_tabulate _ _ _ _ _ fun k j => by split <;> constructor <;> omega,
    entriesWithin_tabulate _ _ _ _ _ fun k j => by split <;> constructor <;> omega⟩

/-- These weights fit the example settings and the system's tables. -/
theorem wellFormed_countingWeights :
    wellFormed exampleSettings lookupTables (countingWeights exampleSettings) = true := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := lookupTables_wellFormed
  obtain ⟨d1, d2, e2⟩ := countingWeights_sizes exampleSettings
  simp only [wellFormed, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, by decide⟩, by decide⟩, by decide⟩, by decide⟩,
    Or.inr (by decide)⟩, by decide⟩, by decide⟩, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩,
    d1⟩, d2⟩, size_tabulate _ _⟩, e2⟩, fun l hl => ?_⟩
  rw [exampleSettings_layer l hl, countingWeights_layer _ l hl]
  apply layerWellFormed_constantLayer
  case routed =>
    intro mix
    have odd := (exampleSettings_isMixture l).mp mix
    simp [exampleLayerSettings, odd]
  all_goals simp [exampleLayerSettings]

/-- These weights are valid at the example settings. -/
theorem weightsAreValid_countingWeights :
    weightsAreValid exampleSettings (countingWeights exampleSettings) = true := by
  simp only [weightsAreValid, weightsInRange, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨wellFormed_countingWeights,
    countingWeights_entries exampleSettings _ _ (by omega) (by omega) _ _ (by omega) (by omega),
    fun l hl => ?_⟩
  rw [countingWeights_layer _ l hl]
  exact layerWeightsInRange_constantLayer _ _ _ (by decide) (by decide)

/-- The made-up weights at the example settings. -/
def countingModelWeights : ModelWeights exampleSettings :=
  ⟨countingWeights exampleSettings, weightsAreValid_countingWeights⟩

/-- **These weights pass the worst-case check.** -/
theorem passesWorstCaseCheck_countingModelWeights :
    PassesWorstCaseCheck exampleSettings countingModelWeights :=
  passesWorstCaseCheck_of_small_entries _ fun l hl =>
    layerWithin_countingWeights exampleSettings 256 (by decide) l hl

/-- The final norm's shift at the example settings is at least 1. -/
theorem finalShift_exampleSettings : 1 ≤ exampleSettings.finalShift := by
  decide +kernel

/-- The final norm's result at the one entry 1,000 is positive, at the example settings. -/
theorem normOfOneEntry_exampleSettings :
    0 < normOfOneEntry exampleSettings.finalBits exampleSettings.finalShift
      exampleSettings.finalEps 1000 := by
  decide +kernel

/-- **At these weights the model counts**: after 1 to 1,024 tokens of the vocabulary its next token
is the last token's rest on division by 5,120, plus 1. -/
theorem modelNextToken_countingModelWeights (earlier : List Nat) (last : Nat)
    (fits : (earlier ++ [last]).length ≤ 1024)
    (inVocabulary : ∀ token ∈ earlier ++ [last], token < 202048) :
    modelNextToken exampleSettings countingModelWeights (earlier ++ [last]) =
      some (last % 5120 + 1) := by
  obtain ⟨next, isNext, _⟩ := modelNextToken_isSome_of_rangeConditionsNeverFail exampleSettings
    countingModelWeights
    (rangeConditionsNeverFail_of_passesWorstCaseCheck _ _ passesWorstCaseCheck_countingModelWeights)
    (earlier ++ [last]) (by simp) fits inVocabulary
  rw [isNext]
  obtain ⟨_, prompt_ok, _, value⟩ := (model_eq_some _ _ _ _ _).mp isNext
  have choice := choice_countingWeights exampleSettings lookupTables (earlier ++ [last]).toArray
    prompt_ok
    (fun l hl => by rw [exampleSettings_layer l hl]; simp [exampleLayerSettings])
    finalShift_exampleSettings (by show 0 < 5120; omega) (by show 5120 < 202048; omega)
    normOfOneEntry_exampleSettings
  have read : (earlier ++ [last]).toArray.entry ((earlier ++ [last]).toArray.size - 1) = last := by
    simp [Array.entry]
  rw [read] at choice
  have same : next = last % 5120 + 1 := value.symm.trans choice
  rw [same]

/-- **The model answers two prompts differently**: 1 after the prompt `[0]`, 2 after `[1]`. -/
theorem modelNextToken_countingModelWeights_apart :
    modelNextToken exampleSettings countingModelWeights [0] = some 1 ∧
      modelNextToken exampleSettings countingModelWeights [1] = some 2 :=
  ⟨modelNextToken_countingModelWeights [] 0 (by decide) (by decide),
    modelNextToken_countingModelWeights [] 1 (by decide) (by decide)⟩

/-- After the prompt `[5]` the output 6, 7, 8 is the model's own, token by token. -/
theorem greedyOutput_countingModelWeights (position : Nat)
    (inOutput : position < [6, 7, 8].length) :
    modelNextToken exampleSettings countingModelWeights ([5] ++ [6, 7, 8].take position) =
      some [6, 7, 8][position] :=
  match position, inOutput with
  | 0, _ => modelNextToken_countingModelWeights [] 5 (by decide) (by decide)
  | 1, _ => modelNextToken_countingModelWeights [5] 6 (by decide) (by decide)
  | 2, _ => modelNextToken_countingModelWeights [5, 6] 7 (by decide) (by decide)

/-! ## 6. One layer of attention whose scores are all 0, at two positions -/

/-- A sum of `n` terms that are all `c`. -/
private theorem sumOver_of_equal_terms (n : Nat) (f : Nat → Int) (c : Int)
    (h : ∀ k, k < n → f k = c) : sumOver n f = n * c := by
  rw [← sumOver_const]
  induction n with
  | zero => rfl
  | succ n step =>
    simp only [sumOver]
    rw [step (fun k inside => h k (by omega)), h n (by omega)]

/-- A sum of two terms. -/
private theorem sumOver_two (f : Nat → Int) : sumOver (1 + 1) f = f 0 + f 1 := by
  show 0 + f 0 + f 1 = f 0 + f 1
  rw [Int.zero_add]

/-- Arrays that are given by equal entries are equal. -/
private theorem tabulate_of_equal_entries {α : Type} [Inhabited α] (n : Nat) (f g : Nat → α)
    (h : ∀ k, k < n → f k = g k) : tabulate n f = tabulate n g := by
  apply Array.ext (by rw [size_tabulate, size_tabulate])
  intro i inFirst inSecond
  have inside : i < n := by rw [size_tabulate] at inFirst; exact inFirst
  rw [← entry_inside _ i inFirst, ← entry_inside _ i inSecond, tabulate_read _ _ _ inside,
    tabulate_read _ _ _ inside, h i inside]

/-- A function that sends 0 to 0, applied to a vector whose reads are all 0. -/
private theorem read_map_of_zero (v : IntegerVector) (f : Int → Int) (atZero : f 0 = 0)
    (h : ∀ k, v.entry k = 0) (k : Nat) : (v.map f).entry k = 0 := by
  by_cases inside : k < v.size
  · rw [map_read _ _ _ inside, h k, atZero]
  · rw [entry_outside _ k (by rw [Array.size_map]; exact inside)]
    rfl

/-- A product with a zero matrix reads 0 everywhere. -/
theorem product_of_zero (a : IntegerVector) (W : Matrix) (outputs : Nat) (zero : MatrixWithin 0 W)
    (j : Nat) : (product a W outputs).entry j = 0 :=
  read_tabulate_of_zero _ _ (fun j => sumOver_of_terms_zero _ _ fun k _ => by
    rw [read_of_matrixWithin_zero W zero, Int.mul_zero]) j

/-- With a zero query matrix every query is 0. -/
theorem projections_query_of_zero (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (t : Nat) (a : IntegerVector) (zero : MatrixWithin 0 w.query)
    (positive : 1 ≤ p.queryShift) (j : Nat) :
    (projections s p tables w t a).query.entry j = 0 := by
  simp only [projections]
  apply read_map_of_zero _ _ (by decide)
  apply read_map_of_zero _ _ (roundShift_of_zero _ positive)
  unfold rotate
  apply read_tabulate_of_zero
  intro j
  simp only [product_of_zero a w.query s.queryWidth zero, Int.mul_zero, Int.sub_self, Int.add_zero,
    ite_self]

/-- A value, from the product with the value matrix. -/
theorem projections_value (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (t : Nat) (a : IntegerVector) (j : Nat) (inside : j < s.keyValueWidth) :
    (projections s p tables w t a).value.entry j =
      clamp (roundShift ((product a w.value s.keyValueWidth).entry j) p.valueShift)
        activationBound := by
  simp only [projections]
  rw [map_read _ _ _ (by rw [Array.size_map, size_product]; exact inside),
    map_read _ _ _ (by rw [size_product]; exact inside)]

/-- If all scores are 0, every exponential is the table's first entry. -/
theorem exponentials_of_zero_scores (tables : Tables) (shift : Nat) (scores : IntegerVector) (i j : Nat)
    (inside : j < scores.size) (zero : ∀ j, scores.entry j = 0)
    (table : 0 < tables.exponential.size) :
    ((scores.map fun sj => (maxUpTo (fun j => scores.entry j) i - sj) / 2 ^ shift).map
      fun (u : Int) =>
        if u < tables.exponential.size then tables.exponential.entry u.toNat else 0).entry j =
      tables.exponential.entry 0 := by
  have top : maxUpTo (fun j => scores.entry j) i = 0 := by
    obtain ⟨place, _, attained⟩ := (maxUpTo_spec (fun j => scores.entry j) i).2
    rw [← attained]
    exact zero place
  rw [map_read _ _ _ (by rw [Array.size_map]; exact inside), map_read _ _ _ inside, top, zero j,
    Int.sub_self, Int.zero_ediv, if_pos (by omega)]
  rfl

/-- **An attention head whose queries are 0, at the second position**: the mean of the two values,
rounded. -/
theorem attendHead_out_of_zero_queries (s : Settings) (p : LayerSettings) (tables : Tables)
    (projected : Array Projections) (h c : Nat) (first second : Int)
    (queries : ∀ j, (projected.entry 1).query.entry j = 0)
    (value0 : (projected.entry 0).value.entry
      (h / (s.queryHeads / s.keyValueHeads) * s.headDim + c) = first)
    (value1 : (projected.entry 1).value.entry
      (h / (s.queryHeads / s.keyValueHeads) * s.headDim + c) = second)
    (inside : c < s.headDim) (table : 0 < tables.exponential.size)
    (positive : 0 < tables.exponential.entry 0) :
    (attendHead s p tables projected 1 h).out.entry c = (2 * (first + second) + 2) / 4 := by
  have scores : ∀ j, (tabulate (1 + 1) fun j => sumOver s.headDim fun c =>
      (projected.entry 1).query.entry (h * s.headDim + c) *
        (projected.entry j).key.entry
          (h / (s.queryHeads / s.keyValueHeads) * s.headDim + c)).entry j = 0 :=
    read_tabulate_of_zero _ _ fun j => sumOver_of_terms_zero _ _ fun c _ => by
      rw [queries, Int.zero_mul]
  have exponential := fun j (below : j < 1 + 1) =>
    exponentials_of_zero_scores tables p.softmaxShift _ 1 j
      (by rw [size_tabulate]; exact below) scores table
  simp only [attendHead]
  rw [map_read _ _ _ (by rw [size_tabulate]; exact inside), tabulate_read _ _ _ inside,
    sumOver_two, sumOver_two, exponential 0 (by omega), exponential 1 (by omega), value0, value1]
  generalize tables.exponential.entry 0 = weight at positive
  have numerator : 2 * (weight * first + weight * second) + (weight + weight) =
      weight * (2 * (first + second) + 2) := by grind
  have denominator : 2 * (weight + weight) = weight * 4 := by omega
  rw [numerator, denominator, Int.mul_ediv_mul_of_pos _ _ positive]

/-! ## 7. A layer that marks -/

/-- A dense layer: the value matrix has 200 at every place, the layer's output matrix has 200 in
column 0, and all other matrices are zero. -/
def markingLayer (s : Settings) : LayerWeights :=
  { constantLayer s 0 false with
    value := constantMatrix s.width s.keyValueWidth 200
    output := tabulate s.queryWidth fun _ => tabulate s.width fun k => if k = 0 then 200 else 0 }

/-- Every value of that layer at a position whose row has `entry` at place 0 and 0 elsewhere. -/
def markValue (p : LayerSettings) (entry : Int) : Int :=
  clamp (roundShift
    (normOfOneEntry p.attentionBits p.attentionShift p.attentionEps entry * 200) p.valueShift)
    activationBound

/-- What that layer's attention adds at place 0 of the second position, if the two rows have `first`
and `second` at place 0 and 0 elsewhere. -/
def markAddition (s : Settings) (p : LayerSettings) (first second : Int) : Int :=
  roundShift (s.queryWidth * ((2 * (markValue p first + markValue p second) + 2) / 4 * 200))
    p.outputShift

/-- The values of the marking layer. -/
theorem value_markingLayer (s : Settings) (p : LayerSettings) (tables : Tables) (t : Nat)
    (entry : Int) (some_width : 0 < s.width) (norm : 1 ≤ p.attentionShift) (j : Nat)
    (inside : j < s.keyValueWidth) :
    (projections s p tables (markingLayer s) t (rmsNorm p.attentionBits p.attentionShift
      p.attentionEps (rowWithOneEntry s.width 0 entry)).out).value.entry j = markValue p entry := by
  have size : (rmsNorm p.attentionBits p.attentionShift p.attentionEps
      (rowWithOneEntry s.width 0 entry)).out.size = s.width := by
    rw [(size_rmsNorm _ _ _ _).2]; exact size_tabulate _ _
  rw [projections_value _ _ _ _ _ _ _ inside]
  unfold product
  rw [tabulate_read _ _ _ inside, size, sumOver_of_one_term s.width 0 _ some_width
    fun k below other => by
      rw [rmsNorm_oneEntry _ _ _ _ _ _ norm some_width k below, if_neg other, Int.zero_mul],
    rmsNorm_oneEntry _ _ _ _ _ _ norm some_width 0 some_width, if_pos rfl]
  simp only [markingLayer, constantMatrix]
  rw [tabulate_read _ _ _ some_width, tabulate_read _ _ _ inside]
  rfl

/-- **Attention of the marking layer at the second of two positions.** -/
theorem attention_out_markingLayer (s : Settings) (p : LayerSettings) (tables : Tables)
    (x : Matrix) (first second : Int) (size : x.size = 1 + 1)
    (row0 : x.entry 0 = rowWithOneEntry s.width 0 first)
    (row1 : x.entry 1 = rowWithOneEntry s.width 0 second)
    (some_width : 0 < s.width) (norm : 1 ≤ p.attentionShift) (query : 1 ≤ p.queryShift)
    (output : 1 ≤ p.outputShift) (divides : s.queryHeads % s.keyValueHeads = 0)
    (table : 0 < tables.exponential.size) (positive : 0 < tables.exponential.entry 0) :
    (attention s p tables (markingLayer s) x).out.entry 1 =
      rowWithOneEntry s.width 0 (second + markAddition s p first second) := by
  have zero : 0 < x.size := by omega
  have one : 1 < x.size := by omega
  have projected : ∀ t, t < x.size → (tabulate x.size fun t =>
      projections s p tables (markingLayer s) t ((x.map fun row =>
        rmsNorm p.attentionBits p.attentionShift p.attentionEps row).entry t).out).entry t =
      projections s p tables (markingLayer s) t
        (rmsNorm p.attentionBits p.attentionShift p.attentionEps (x.entry t)).out :=
    fun t inside => by rw [tabulate_read _ _ _ inside, map_read _ _ _ inside]
  have noQuery : MatrixWithin 0 (markingLayer s).query :=
    matrixWithin_constantMatrix _ _ _ _ (by decide)
  have head : ∀ j, j < s.queryWidth → (attendHead s p tables (tabulate x.size fun t =>
      projections s p tables (markingLayer s) t ((x.map fun row =>
        rmsNorm p.attentionBits p.attentionShift p.attentionEps row).entry t).out) 1
      (j / s.headDim)).out.entry (j % s.headDim) =
      (2 * (markValue p first + markValue p second) + 2) / 4 := by
    intro j inside
    obtain ⟨inHeads, inHead⟩ := split_index s.queryHeads s.headDim j inside
    have place := head_index s.keyValueHeads s.headDim _ _
      (group_index s.queryHeads s.keyValueHeads _ divides inHeads) inHead
    apply attendHead_out_of_zero_queries s p tables _ _ _ _ _ _ _ _ inHead table positive
    · intro j
      rw [projected 1 one]
      exact projections_query_of_zero s p tables _ _ _ noQuery query j
    · rw [projected 0 zero, row0]
      exact value_markingLayer s p tables 0 first some_width norm _ place
    · rw [projected 1 one, row1]
      exact value_markingLayer s p tables 1 second some_width norm _ place
  simp only [attention]
  rw [tabulate_read _ _ _ one, map_read _ _ _ (by rw [size_tabulate]; exact one),
    tabulate_read _ _ _ one, row1]
  unfold addVectors rowWithOneEntry
  rw [size_tabulate]
  apply tabulate_of_equal_entries
  intro k below
  rw [tabulate_read _ _ _ below, map_read _ _ _ (by rw [size_product]; exact below)]
  unfold product
  rw [tabulate_read _ _ _ below, size_tabulate,
    sumOver_of_equal_terms s.queryWidth _
      ((2 * (markValue p first + markValue p second) + 2) / 4 * if k = 0 then 200 else 0)
      fun j inside => by
        rw [tabulate_read _ _ _ inside, tabulate_read _ _ _ one,
          tabulate_read _ _ _ (split_index s.queryHeads s.headDim j inside).1, head j inside]
        simp only [markingLayer]
        rw [tabulate_read _ _ _ inside, tabulate_read _ _ _ below]]
  by_cases here : k = 0
  · rw [if_pos here, if_pos here, if_pos here]
    rfl
  · rw [if_neg here, if_neg here, if_neg here, Int.mul_zero, Int.mul_zero,
      roundShift_of_zero _ output, Int.add_zero]

/-! ## 8. Weights at which an earlier token matters, at any settings -/

/-- If `f` is 0 at all indices below `n`, the argmax is 0. -/
theorem firstArgmax_of_all_zero (f : Nat → Int) (n : Nat) (some : 0 < n)
    (h : ∀ v, v < n → f v = 0) : firstArgmax f n = 0 := by
  obtain ⟨below, _, least⟩ := firstArgmax_spec f n some
  apply Classical.byContradiction
  intro other
  have smaller := least 0 (by omega)
  rw [h 0 some, h _ below] at smaller
  omega

/-- A layer whose down matrices are zero returns what its attention returns. -/
theorem layer_out_of_zero_down (s : Settings) (tables : Tables) (weights : Weights) (l : Nat)
    (x : Matrix) (shared : MatrixWithin 0 (weights.perLayer.entry l).shared.down)
    (routed : ∀ e, MatrixWithin 0 ((weights.perLayer.entry l).routed.entry e).down)
    (down : 1 ≤ (s.perLayer.entry l).downShift) :
    (layer s tables weights l x).out =
      (attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) x).out := by
  simp only [layer]
  rw [Array.map_map]
  have same : ((fun ff : FeedForward => ff.out) ∘ fun row =>
      feedForward s (s.perLayer.entry l) tables (weights.perLayer.entry l) (s.isMixture l) row) =
      id :=
    funext fun row => feedForward_out_of_zero s _ tables _ _ row shared routed down
  rw [same, Array.map_id]

/-- If all layers but the first add nothing, the stream above one layer or more is what the first
layer returns. -/
theorem streamAbove_of_zero_above_first (s : Settings) (tables : Tables) (weights : Weights)
    (x0 : Matrix)
    (zero : ∀ l, 0 < l → l < s.layers → LayerWithin 0 (weights.perLayer.entry l))
    (shifts : ∀ l, l < s.layers →
      1 ≤ (s.perLayer.entry l).outputShift ∧ 1 ≤ (s.perLayer.entry l).downShift)
    (l : Nat) (inside : l + 1 ≤ s.layers) :
    streamAbove x0 (firstLayers s tables weights x0 (l + 1)) =
      (layer s tables weights 0 x0).out := by
  induction l with
  | zero => rw [streamAbove_succ, streamAbove_zero]
  | succ l step =>
    rw [streamAbove_succ, step (by omega)]
    exact layer_out_of_zero s tables weights (l + 1) _ (zero (l + 1) (by omega) inside)
      (shifts (l + 1) inside).1 (shifts (l + 1) inside).2

/-- Made-up weights. The embedding sends token 0 to the row with 1,000 at place 0 and every other
token to the zero row; the first layer is `markingLayer`; all matrices of the other layers are
zero; the head matrix has 1 at row `k`, column `k + 1`. -/
def markingWeights (s : Settings) : Weights where
  embedding := tabulate s.vocabulary fun token => tabulate s.width fun k =>
    if k = 0 then (if token = 0 then 1000 else 0) else 0
  perLayer := tabulate s.layers fun l =>
    if l = 0 then markingLayer s else constantLayer s 0 (s.isMixture l)
  head := tabulate s.width fun k => tabulate s.vocabulary fun v => if v = k + 1 then 1 else 0

/-- The first layer of these weights. -/
theorem markingWeights_first (s : Settings) (h : 0 < s.layers) :
    (markingWeights s).perLayer.entry 0 = markingLayer s := by
  simp only [markingWeights]
  rw [tabulate_read _ _ _ h, if_pos rfl]

/-- The other layers of these weights. -/
theorem markingWeights_layer (s : Settings) (l : Nat) (above : 0 < l) (h : l < s.layers) :
    (markingWeights s).perLayer.entry l = constantLayer s 0 (s.isMixture l) := by
  simp only [markingWeights]
  rw [tabulate_read _ _ _ h, if_neg (by omega)]

/-- What the embedding of these weights has at place 0 of a token's row. -/
def embeddedMark (token : Nat) : Int := if token = 0 then 1000 else 0

/-- The entry at place 0 of the last stream's second row, on a prompt of two tokens. -/
def markedEntry (s : Settings) (first last : Nat) : Int :=
  embeddedMark last + markAddition s (s.perLayer.entry 0) (embeddedMark first) (embeddedMark last)

/-- **The greedy choice at these weights after two tokens** is that of a row with one entry. -/
theorem choice_markingWeights (s : Settings) (tables : Tables) (first last : Nat)
    (firstToken : first < s.vocabulary) (lastToken : last < s.vocabulary)
    (some_layer : 0 < s.layers) (some_width : 0 < s.width)
    (shifts : ∀ l, l < s.layers →
      1 ≤ (s.perLayer.entry l).outputShift ∧ 1 ≤ (s.perLayer.entry l).downShift)
    (norm : 1 ≤ (s.perLayer.entry 0).attentionShift) (query : 1 ≤ (s.perLayer.entry 0).queryShift)
    (divides : s.queryHeads % s.keyValueHeads = 0)
    (table : 0 < tables.exponential.size) (positive : 0 < tables.exponential.entry 0) :
    (trace s tables (markingWeights s) #[first, last]).choices.entry 1 =
      firstArgmax (fun v => (product (rmsNorm s.finalBits s.finalShift s.finalEps
        (rowWithOneEntry s.width 0 (markedEntry s first last))).out
        (countingWeights s).head s.vocabulary).entry v) s.vocabulary := by
  obtain ⟨above, layers⟩ : ∃ above, s.layers = above + 1 := ⟨s.layers - 1, by omega⟩
  have row : ∀ token, token < s.vocabulary → (markingWeights s).embedding.entry token =
      rowWithOneEntry s.width 0 (embeddedMark token) := by
    intro token inside
    simp only [markingWeights]
    rw [tabulate_read _ _ _ inside]
    rfl
  have noDown : MatrixWithin 0 ((markingWeights s).perLayer.entry 0).shared.down := by
    rw [markingWeights_first s some_layer]
    exact matrixWithin_constantMatrix _ _ _ _ (by decide)
  have noRouted : ∀ e,
      MatrixWithin 0 (((markingWeights s).perLayer.entry 0).routed.entry e).down := by
    intro e
    rw [markingWeights_first s some_layer]
    exact matrixWithin_empty 0 (Int.le_refl 0)
  have stream := streamAbove_of_zero_above_first s tables (markingWeights s)
    (#[first, last].map fun token => (markingWeights s).embedding.entry token)
    (fun l positive inside => by
      rw [markingWeights_layer s l positive inside]
      exact layerWithin_constantLayer _ _ _ _ (by decide))
    shifts above (by omega)
  rw [← layers, layer_out_of_zero_down s tables _ 0 _ noDown noRouted (shifts 0 some_layer).2,
    markingWeights_first s some_layer] at stream
  have size : ((attention s (s.perLayer.entry 0) tables (markingLayer s)
      (#[first, last].map fun token => (markingWeights s).embedding.entry token)).out).size =
      1 + 1 := by
    rw [(size_attention _ _ _ _ _).2.2.2.2.2, Array.size_map]
    rfl
  have second := attention_out_markingLayer s (s.perLayer.entry 0) tables
    (#[first, last].map fun token => (markingWeights s).embedding.entry token)
    (embeddedMark first) (embeddedMark last) (by rw [Array.size_map]; rfl)
    (by rw [map_read _ _ _ (by show 0 < 2; omega)]; exact row first firstToken)
    (by rw [map_read _ _ _ (by show 1 < 2; omega)]; exact row last lastToken)
    some_width norm query (shifts 0 some_layer).1 divides table positive
  simp only [trace]
  rw [stream,
    map_read _ _ _ (by simp only [Array.size_map, size]; omega),
    map_read _ _ _ (by simp only [Array.size_map, size]; omega),
    map_read _ _ _ (by rw [size]; omega), second]
  rfl

/-- The greedy choice at a row with one entry at place 0 whose norm is positive: token 1. -/
theorem choice_of_positive_entry (s : Settings) (value : Int) (some_width : 0 < s.width)
    (finalShift : 1 ≤ s.finalShift) (tokens : 1 < s.vocabulary)
    (positive : 0 < normOfOneEntry s.finalBits s.finalShift s.finalEps value) :
    firstArgmax (fun v => (product (rmsNorm s.finalBits s.finalShift s.finalEps
      (rowWithOneEntry s.width 0 value)).out (countingWeights s).head s.vocabulary).entry v)
      s.vocabulary = 1 := by
  apply firstArgmax_of_one_positive _ _ _ tokens
  · rw [logit_countingWeights s 0 value some_width finalShift 1 tokens, if_pos rfl]
    exact positive
  · intro v token other
    rw [logit_countingWeights s 0 value some_width finalShift v token, if_neg other]

/-- The greedy choice at a row with one entry at place 0 whose norm is 0: token 0. -/
theorem choice_of_zero_entry (s : Settings) (value : Int) (some_width : 0 < s.width)
    (finalShift : 1 ≤ s.finalShift) (tokens : 1 < s.vocabulary)
    (zero : normOfOneEntry s.finalBits s.finalShift s.finalEps value = 0) :
    firstArgmax (fun v => (product (rmsNorm s.finalBits s.finalShift s.finalEps
      (rowWithOneEntry s.width 0 value)).out (countingWeights s).head s.vocabulary).entry v)
      s.vocabulary = 0 := by
  apply firstArgmax_of_all_zero _ _ (by omega)
  intro v token
  rw [logit_countingWeights s 0 value some_width finalShift v token, zero, ite_self]

/-- Layer 0 is dense at all settings. -/
theorem isMixture_zero (s : Settings) : s.isMixture 0 = false := by
  simp [Settings.isMixture]

/-- The marking layer is well formed as a dense layer, if every `eps` and every shift that the layer
hands to `roundShift` is at least 1. -/
theorem layerWellFormed_markingLayer (s : Settings) (p : LayerSettings)
    (eps1 : 1 ≤ p.attentionEps) (eps2 : 1 ≤ p.feedForwardEps)
    (shift1 : 1 ≤ p.attentionShift) (query : 1 ≤ p.queryShift) (key : 1 ≤ p.keyShift)
    (valueShift : 1 ≤ p.valueShift) (output : 1 ≤ p.outputShift)
    (shift2 : 1 ≤ p.feedForwardShift) (gate : 1 ≤ p.gateShift) (up : 1 ≤ p.upShift)
    (down : 1 ≤ p.downShift) : layerWellFormed s p (markingLayer s) false = true := by
  simp only [layerWellFormed, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hasSize_constantMatrix _ _ _, hasSize_constantMatrix _ _ _⟩,
    hasSize_constantMatrix _ _ _⟩, hasSize_tabulate _ _ _⟩, eps1⟩, eps2⟩, shift1⟩, query⟩,
    key⟩, valueShift⟩, output⟩, shift2⟩, gate⟩, up⟩, down⟩, ?_⟩
  simp only [Bool.false_eq_true, if_false, markingLayer, constantLayer]
  exact hasSizes_constantGated _ _ _

/-- The matrices of the marking layer contain weights of 13 bits. -/
theorem layerWeightsInRange_markingLayer (s : Settings) :
    layerWeightsInRange false (markingLayer s) = true := by
  have base := layerWeightsInRange_constantLayer s 0 false (by decide) (by decide)
  simp only [layerWeightsInRange, Bool.and_eq_true] at base ⊢
  exact ⟨⟨⟨⟨⟨base.1.1.1.1.1, base.1.1.1.1.2⟩,
    entriesWithin_constantMatrix _ _ _ _ _ (by decide) (by decide)⟩,
    entriesWithin_tabulate _ _ _ _ _ fun _ _ => by split <;> constructor <;> omega⟩,
    base.1.2⟩, base.2⟩

/-- The matrices of the marking layer are within 200. -/
theorem layerWithin_markingLayer (s : Settings) : LayerWithin 200 (markingLayer s) := by
  have base := layerWithin_constantLayer s 0 200 false (by decide)
  exact ⟨base.1, base.2.1, matrixWithin_constantMatrix _ _ _ _ (by decide),
    matrixWithin_tabulate _ _ _ _ (by decide) (fun _ _ => by split <;> decide),
    base.2.2.2.2.1, base.2.2.2.2.2.1, base.2.2.2.2.2.2⟩

/-- The sizes of the embedding, of the head matrix and of the array of layers. -/
theorem markingWeights_sizes (s : Settings) :
    hasSize s.vocabulary s.width (markingWeights s).embedding = true ∧
    hasSize s.width s.vocabulary (markingWeights s).head = true ∧
    (markingWeights s).perLayer.size = s.layers :=
  ⟨hasSize_tabulate _ _ _, hasSize_tabulate _ _ _, size_tabulate _ _⟩

/-- The entries of the embedding are in 0 .. 1,000, and those of the head matrix in 0 .. 1. -/
theorem markingWeights_entries (s : Settings) (low high : Int) (lower : low ≤ 0)
    (upper : 1000 ≤ high) (low' high' : Int) (lower' : low' ≤ 0) (upper' : 1 ≤ high') :
    entriesWithin low high (markingWeights s).embedding = true ∧
    entriesWithin low' high' (markingWeights s).head = true :=
  ⟨entriesWithin_tabulate _ _ _ _ _ fun k j => by
      split
      · split <;> constructor <;> omega
      · constructor <;> omega,
    entriesWithin_tabulate _ _ _ _ _ fun k j => by split <;> constructor <;> omega⟩

/-! ## 9. These weights at the example settings -/

/-- A layer of zero matrices is well formed at the example settings. -/
theorem layerWellFormed_zeroLayer_exampleSettings (l : Nat) :
    layerWellFormed exampleSettings (exampleLayerSettings l)
      (constantLayer exampleSettings 0 (exampleSettings.isMixture l))
      (exampleSettings.isMixture l) = true := by
  apply layerWellFormed_constantLayer
  case routed =>
    intro mix
    have odd := (exampleSettings_isMixture l).mp mix
    simp [exampleLayerSettings, odd]
  all_goals simp [exampleLayerSettings]

/-- These weights fit the example settings and the system's tables. -/
theorem wellFormed_markingWeights :
    wellFormed exampleSettings lookupTables (markingWeights exampleSettings) = true := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := lookupTables_wellFormed
  obtain ⟨d1, d2, e2⟩ := markingWeights_sizes exampleSettings
  simp only [wellFormed, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, by decide⟩, by decide⟩, by decide⟩, by decide⟩,
    Or.inr (by decide)⟩, by decide⟩, by decide⟩, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩,
    d1⟩, d2⟩, size_tabulate _ _⟩, e2⟩, fun l hl => ?_⟩
  by_cases first : l = 0
  · subst first
    rw [exampleSettings_layer 0 hl, markingWeights_first _ hl, isMixture_zero]
    apply layerWellFormed_markingLayer
    all_goals simp [exampleLayerSettings]
  · rw [exampleSettings_layer l hl, markingWeights_layer _ l (by omega) hl]
    exact layerWellFormed_zeroLayer_exampleSettings l

/-- These weights are valid at the example settings. -/
theorem weightsAreValid_markingWeights :
    weightsAreValid exampleSettings (markingWeights exampleSettings) = true := by
  simp only [weightsAreValid, weightsInRange, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨wellFormed_markingWeights,
    markingWeights_entries exampleSettings _ _ (by omega) (by omega) _ _ (by omega) (by omega),
    fun l hl => ?_⟩
  by_cases first : l = 0
  · subst first
    rw [markingWeights_first _ hl, isMixture_zero]
    exact layerWeightsInRange_markingLayer _
  · rw [markingWeights_layer _ l (by omega) hl]
    exact layerWeightsInRange_constantLayer _ _ _ (by decide) (by decide)

/-- The made-up weights at the example settings. -/
def markingModelWeights : ModelWeights exampleSettings :=
  ⟨markingWeights exampleSettings, weightsAreValid_markingWeights⟩

/-- A layer within a bound is within every larger bound. -/
private theorem layerWithin_of_le (small large : Int) (le : small ≤ large) (layer : LayerWeights)
    (within : LayerWithin small layer) : LayerWithin large layer := by
  have matrix : ∀ W, MatrixWithin small W → MatrixWithin large W :=
    fun _ h k j => Int.le_trans (h k j) le
  have gated : ∀ w, GatedWithin small w → GatedWithin large w :=
    fun _ h => ⟨matrix _ h.1, matrix _ h.2.1, matrix _ h.2.2⟩
  exact ⟨matrix _ within.1, matrix _ within.2.1, matrix _ within.2.2.1, matrix _ within.2.2.2.1,
    gated _ within.2.2.2.2.1, matrix _ within.2.2.2.2.2.1,
    fun expert => gated _ (within.2.2.2.2.2.2 expert)⟩

/-- **These weights pass the worst-case check.** -/
theorem passesWorstCaseCheck_markingModelWeights :
    PassesWorstCaseCheck exampleSettings markingModelWeights := by
  apply passesWorstCaseCheck_of_small_entries
  intro l hl
  show LayerWithin 256 ((markingWeights exampleSettings).perLayer.entry l)
  by_cases first : l = 0
  · subst first
    rw [markingWeights_first _ hl]
    exact layerWithin_of_le 200 256 (by decide) _ (layerWithin_markingLayer _)
  · rw [markingWeights_layer _ l (by omega) hl]
    exact layerWithin_constantLayer _ _ _ _ (by decide)

/-- At the example settings the final norm's result at place 0 of the last stream's second row is
positive after the tokens 0, 1, and 0 after the tokens 1, 1. -/
theorem markedEntry_exampleSettings :
    0 < normOfOneEntry exampleSettings.finalBits exampleSettings.finalShift
      exampleSettings.finalEps (markedEntry exampleSettings 0 1) ∧
    normOfOneEntry exampleSettings.finalBits exampleSettings.finalShift
      exampleSettings.finalEps (markedEntry exampleSettings 1 1) = 0 := by
  decide +kernel

/-! The numbers on the way: the values of the first layer at the two kinds of row, their rounded
mean, and the entry at place 0 of the last stream's second row. -/
example : markValue (exampleLayerSettings 0) 1000 = 3 ∧
    markValue (exampleLayerSettings 0) 0 = 0 ∧ (2 * (3 + 0) + 2) / 4 = (2 : Int) ∧
    markedEntry exampleSettings 0 1 = 4 ∧ markedEntry exampleSettings 1 1 = 0 := by
  decide +kernel

/-- The model's next token at these weights after two tokens, as the greedy choice at a row with one
entry. -/
theorem modelNextToken_markingModelWeights_eq (first last : Nat) (firstToken : first < 202048)
    (lastToken : last < 202048) :
    modelNextToken exampleSettings markingModelWeights [first, last] =
      some (firstArgmax (fun v => (product (rmsNorm exampleSettings.finalBits
        exampleSettings.finalShift exampleSettings.finalEps
        (rowWithOneEntry exampleSettings.width 0 (markedEntry exampleSettings first last))).out
        (countingWeights exampleSettings).head exampleSettings.vocabulary).entry v)
        exampleSettings.vocabulary) := by
  obtain ⟨_, _, table, positive, _⟩ := lookupTables_wellFormed
  obtain ⟨next, isNext, _⟩ := modelNextToken_isSome_of_rangeConditionsNeverFail exampleSettings
    markingModelWeights
    (rangeConditionsNeverFail_of_passesWorstCaseCheck _ _ passesWorstCaseCheck_markingModelWeights)
    [first, last] (by show 0 < 2; omega) (by show 2 ≤ 1024; omega) (by
      intro token inList
      rcases List.mem_cons.mp inList with isFirst | rest
      · rw [isFirst]; exact firstToken
      · rw [List.mem_singleton.mp rest]; exact lastToken)
  rw [isNext]
  obtain ⟨_, _, _, value⟩ := (model_eq_some _ _ _ _ _).mp isNext
  have choice := choice_markingWeights exampleSettings lookupTables first last firstToken
    lastToken (by show 0 < 48; omega) (by show 0 < 5120; omega)
    (fun l hl => by rw [exampleSettings_layer l hl]; simp [exampleLayerSettings])
    (by rw [exampleSettings_layer 0 (by omega)]; simp [exampleLayerSettings])
    (by rw [exampleSettings_layer 0 (by omega)]; simp [exampleLayerSettings])
    (by decide) table positive
  exact congrArg some (value.symm.trans choice)

/-- **An earlier token matters.** The prompts `[0, 1]` and `[1, 1]` end in the same token, and the
model answers them differently: with 1 and with 0. -/
theorem modelNextToken_markingModelWeights_apart :
    modelNextToken exampleSettings markingModelWeights [0, 1] = some 1 ∧
      modelNextToken exampleSettings markingModelWeights [1, 1] = some 0 := by
  obtain ⟨marked, unmarked⟩ := markedEntry_exampleSettings
  constructor
  · rw [modelNextToken_markingModelWeights_eq 0 1 (by omega) (by omega),
      choice_of_positive_entry exampleSettings _ (by show 0 < 5120; omega)
        finalShift_exampleSettings (by show 1 < 202048; omega) marked]
  · rw [modelNextToken_markingModelWeights_eq 1 1 (by omega) (by omega),
      choice_of_zero_entry exampleSettings _ (by show 0 < 5120; omega)
        finalShift_exampleSettings (by show 1 < 202048; omega) unmarked]

end VerifiableInference.Bounds

#print axioms VerifiableInference.Bounds.passesWorstCaseCheck_countingModelWeights
#print axioms VerifiableInference.Bounds.modelNextToken_countingModelWeights
#print axioms VerifiableInference.Bounds.modelNextToken_countingModelWeights_apart
#print axioms VerifiableInference.Bounds.greedyOutput_countingModelWeights
#print axioms VerifiableInference.Bounds.passesWorstCaseCheck_markingModelWeights
#print axioms VerifiableInference.Bounds.modelNextToken_markingModelWeights_apart
