-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/SomeWeightsPass.lean

The worst-case check is not empty: a family of weights passes it, and the family has a member in
which no matrix is zero.
- `passesWorstCaseCheck_of_uniformCheck`: at any settings, if `uniformCheck`
  (IntegerModel/Bounds/UniformCheck.lean) passes for a number `entry`, then all weights pass whose
  layers' matrices have every entry in `-entry .. entry`. Their embedding and their head matrix
  (`weights.head`: from the last stream to the logits) are free, within `weightsAreValid`.
- `exampleSettings`: the sizes that the weights' type asks for; every shift and every number of the
  norms follows from the rule that stands in part 2 of this file, out of Lean's ranges, the tests'
  formulas and tests on made-up weights; valid settings (`exampleSettings_valid`).
- `passesWorstCaseCheck_of_small_entries`: the instance at these settings, with 256.
- `constantModelWeights`: made-up weights with 256 at every place of every matrix. They are valid
  and pass (`passesWorstCaseCheck_constantModelWeights`), so the model never fails at them
  (`modelNeverFails_constantModelWeights`).
What the named member shows: that the family is not empty and holds weights without a zero matrix.
It shows little of the model: all columns of its head matrix are equal, so all logits of a
position are equal. The family itself leaves the embedding and the head matrix free.
Limits: the weights are made up. The shifts and the norms' numbers of the settings follow from the
rule in part 2. Three places have the reference table's number, and the settings may depend on
Llama 2 7B and Llama 4 Maverick as far as those three places do: the value shift is fixed by a test
that stood while the example still had the reference table's shifts (THIRD_PARTY.md). Nine of the
sizes are those of Llama 4 Maverick's text model (`hasModelSizes`). Most shifts stand at the upper
ends of their ranges; nothing says that a model at such settings computes anything of use. 256 is
the largest power of two that passes: 409 passes, 410 does not. `exampleSettings_valid` and
`uniformCheck_exampleSettings` are evaluated by Lean's kernel (`decide +kernel`). The file imports
Lean's core and the model's own files. Nothing here is about a trained model's weights.
-/
import IntegerModel.Bounds.UniformCheck
import VerifiableInference.Bounds.NeverFails

set_option autoImplicit false

namespace VerifiableInference.Bounds

open IntegerTransformer IntegerTransformer.Bounds

/-! ## 1. What the check needs of the five tables -/

/-- A read of the empty vector gives 0. -/
theorem read_default (j : Nat) : (default : IntegerVector).entry j = 0 := by
  rfl

/-- A matrix that is given entry by entry is within a bound that all its entries meet. -/
theorem matrixWithin_tabulate (rows columns : Nat) (f : Nat → Nat → Int) (bound : Int)
    (nonneg : 0 ≤ bound) (h : ∀ k j, magnitude (f k j) ≤ bound) :
    MatrixWithin bound (tabulate rows fun k => tabulate columns fun j => f k j) := by
  have zero : magnitude 0 ≤ bound := by rw [magnitude_le_iff]; omega
  intro k j
  by_cases row : k < rows
  · rw [tabulate_read _ _ _ row]
    by_cases column : j < columns
    · rw [tabulate_read _ _ _ column]; exact h k j
    · rw [entry_outside _ j (by rw [size_tabulate]; exact column)]; exact zero
  · rw [entry_outside _ k (by rw [size_tabulate]; exact row), read_default]; exact zero

/-- The largest absolute value of a vector that is given entry by entry. -/
theorem largestMagnitude_tabulate_le (n : Nat) (f : Nat → Int) (bound : Int) (nonneg : 0 ≤ bound)
    (h : ∀ k, magnitude (f k) ≤ bound) : largestMagnitude (tabulate n f) ≤ bound := by
  apply maxUpTo_le
  intro k _
  by_cases inside : k < n
  · rw [tabulate_read _ _ _ inside]; exact h k
  · rw [entry_outside _ k (by rw [size_tabulate]; exact inside)]
    show magnitude 0 ≤ bound
    rw [magnitude_le_iff]; omega

/-- Every entry of the cosine table is in -4,096 .. 4,096: the table's text clamps it. -/
theorem cosineTable_within : MatrixWithin 4096 lookupTables.cosine := by
  simp only [lookupTables, cosineTable]
  apply matrixWithin_tabulate _ _ _ _ (by decide)
  exact fun _ _ => magnitude_clamp_le _ _ (by decide)

/-- Every entry of the sine table is in -4,096 .. 4,096. -/
theorem sineTable_within : MatrixWithin 4096 lookupTables.sine := by
  simp only [lookupTables, sineTable]
  apply matrixWithin_tabulate _ _ _ _ (by decide)
  exact fun _ _ => magnitude_clamp_le _ _ (by decide)

/-- Every entry of the SiLU table is in -4,095 .. 4,095. -/
theorem siluTable_within : largestMagnitude lookupTables.silu.entries ≤ 4095 := by
  simp only [lookupTables, siluTable]
  apply largestMagnitude_tabulate_le _ _ _ (by decide)
  exact fun _ => magnitude_clamp_le _ _ (by decide)

/-- Every entry of the sigmoid table is in 0 .. 65,536. -/
theorem sigmoidTable_within : largestMagnitude lookupTables.sigmoid.entries ≤ 65536 := by
  simp only [lookupTables, sigmoidTable]
  apply largestMagnitude_tabulate_le _ _ _ (by decide)
  intro index
  rw [magnitude_le_iff]
  omega

/-- So a routed expert's input stays in the box. -/
theorem routedInputFits_lookupTables : routedInputFits lookupTables = true := by
  simp only [routedInputFits, decide_eq_true_eq]
  have step : largestMagnitude lookupTables.sigmoid.entries * activationBound ≤
      65536 * activationBound :=
    Int.mul_le_mul_of_nonneg_right sigmoidTable_within (by decide)
  exact Int.le_trans (roundShift_le_roundShift _ _ 16 step) (by decide)

/-! ## 2. Settings

The shifts and the norms' numbers of the example settings follow from the rule below.
The rule takes as inputs the ranges of `settingsAreValid`
(VerifiableInference/ModelWeights.lean), the formulas of the two uniform tests
(`uniformCheck`, IntegerModel/Bounds/UniformCheck.lean; `uniformLengthCheck`,
IntegerModel/Bounds/UniformLengthCheck.lean), and seven tests,
which are listed after the rule. In three places the table has the number of the
library's reference table of scales (`referenceSettings`,
VerifiableInference/ModelGuardsAtReference.lean): the value shift, the down shift and
`bits - shift` of the norms. By the rule these follow from 2, 1 and 4 below. The value
shift is fixed by test (d), a test that stood while the example still had the
reference table's shifts; (d) holds at the reference table too (by the same
arithmetic; no theorem here). With the value shift and `bits - shift` shared, these
figures that the files print for the example are the reference table's own at the same
made-up weights (same arithmetic, no theorem): 229, 36,631 and 327,440 at the weights
with 4,095 at every place, and 18,316 there with 18 for the value shift; 3 and 0, and
their rounded mean 2, at the marking weights.

1. A shift stands at the upper end of its range, the same in all layers. A shift `k` divides by
   `2^k`. In every formula of the two uniform tests a shift occurs only as the divisor of a bound,
   which must stay below a fixed limit or is added to the stream's bound. So a larger shift never
   makes one of these two tests harder (no theorem says so), and the upper end is the value that the
   range itself names and that leaves the largest family of weights. This gives 32 for queries and
   keys, 19 for the output and down projections, 24 for gates and up projections, and in a mixture
   layer 24 for the router and the routed expert's gate and up projection. The softmax shift occurs
   in no formula of the two uniform tests; it follows the same rule, so that there is no second rule
   for it: 12.
2. The one exception is the value shift: the largest in its range at which test (d) holds, 17. Test
   (d) is a control: at the weights with 4,095 at every place the model must fail, by a wide value
   above 32,767. At 18 that value is 18,316, and at the upper end, 24, the control can hold for no
   norm.
3. A norm's shift stands at the upper end of its range, 32. The root of the row's sum of squares,
   which can come near `2^39`, is divided by `2^(shift + 1)` in range condition 2, in the ball's
   radius and in test (g).
4. A norm's bits stand at the upper end that the ranges leave at that shift, 46: they ask
   `bits ≤ shift + 14` and `bits ≤ 47`. `bits - shift` is the scale of a norm's result: the larger
   it is, the more a norm lets through (tests (e), (f)), and the larger the first family can be
   beside test (d).
5. Every eps is `2^24`: the middle of the range `1 ≤ eps < 2^48`, counted in exponents; a power of
   two whose root, 4,096, is a whole number. With a root of 1 test (g) would fail; with a large eps
   a norm would swallow small rows (tests (e), (f)).
6. All norms have the same three numbers: the two of each layer and the final one. No range, formula
   or test asks for a difference.

What validity forces, and no more structure than that: the sizes, the rotary scale and the layers
without a rotary step are those of `hasModelSizes`; the router's three shifts are 0 in a dense
layer; each group of four layers has one softmax shift; `perLayer` has 48 entries.

The tests are this folder's own choice, and they shape the table: above all (d) fixes the
value shift. (a) The settings are valid: `exampleSettings_valid`. (b) `uniformCheck` passes
for a bound on the entries of at least 64: `uniformCheck_exampleSettings`. (c)
`uniformLengthCheck` passes for such a bound: `uniformLengthCheck_exampleSettings`
(VerifiableInference/Bounds/SomeWeightsPassLengthCheck.lean). (d) At the weights with 4,095
at every place the model fails: `not_allConditionsHold_largeConstantModelWeights`
(VerifiableInference/Bounds/SomeWeightsDoNotPass.lean). (e) The last token counts and (f) an
earlier token counts, at made-up weights: `normOfOneEntry_exampleSettings`,
`markedEntry_exampleSettings`
(VerifiableInference/Bounds/PassingWeightsTellPromptsApart.lean). (g) A norm's three numbers
meet `2^(bits - shift) (1 + 1/q) + (2^39 + q + 2) / 2^(shift + 1) + 1/2 ≤ 32,639` with
`q = integerSquareRoot eps`: this is the programs' worst-case test of a norm's quotient
(scales/worst-case-bounds.md); an example below. The bound that a family's theorem carries
is the largest power of two that passes: 256 in (b), 2,048 in (c). In (b) 409 passes and 410
does not, in (c) 3,574 passes and 3,575 does not; that every bound in the tests grows with
the entries' bound is no theorem here. The weights in (f) have the entry 200, which is
within the bound of (b); they are defined at all settings, and 200 is no figure of this
table.

The rule's second part is for a table of 1 to 6 at which a test fails. It names the number that
moves, its direction and its step: for (g) eps up by two exponents at a time, then a norm's bits
down by 1; for (d) the value shift down by 1; for (b) and (c) a norm's bits down by 1 if the part
that refuses is a norm's; for (e) eps down by two exponents at a time; for (f) the output shift down
by 1, then eps down. At the table of 1 to 6 all seven tests hold, so the second part moves nothing.
-/

/-- The quantization parameters of layer `l` of the example, by the rule above. The same in all
layers, but for the rotary step (off in each fourth layer) and the router's three shifts (0 in a
dense layer). -/
def exampleLayerSettings (l : Nat) : LayerSettings where
  attentionBits := 46
  attentionShift := 32
  attentionEps := 2 ^ 24
  queryShift := 32
  keyShift := 32
  valueShift := 17
  rotary := l % 4 != 3
  softmaxShift := 12
  outputShift := 19
  feedForwardBits := 46
  feedForwardShift := 32
  feedForwardEps := 2 ^ 24
  gateShift := 24
  upShift := 24
  downShift := 19
  routerShift := if l % 2 = 1 then 24 else 0
  routedGateShift := if l % 2 = 1 then 24 else 0
  routedUpShift := if l % 2 = 1 then 24 else 0

/-- Example settings of full size. The sizes are those that the weights' type asks for
(`hasModelSizes`): nine of them are those of Llama 4 Maverick's text model. The shifts and the
norms' numbers follow from the rule above. -/
def exampleSettings : Settings where
  positions := 1024
  layers := 48
  width := 5120
  queryHeads := 40
  keyValueHeads := 8
  headDim := 128
  hidden := 16384
  expertHidden := 8192
  experts := 128
  vocabulary := 202048
  rotaryScale := 12
  finalEps := 2 ^ 24
  finalBits := 46
  finalShift := 32
  perLayer := tabulate 48 exampleLayerSettings

/-- The example settings are valid. -/
theorem exampleSettings_valid : settingsAreValid exampleSettings = true := by
  decide +kernel

/-- At the example settings `uniformCheck` passes for layers' matrices with entries in -256 .. 256
and any embedding that `weightsInRange` admits. -/
theorem uniformCheck_exampleSettings :
    uniformCheck exampleSettings 4096 4095 256 2155905152 = true := by
  decide +kernel

/-! The test passes at 409 and refuses at 410. -/
example : uniformCheck exampleSettings 4096 4095 409 2155905152 = true := by decide +kernel
example : uniformCheck exampleSettings 4096 4095 410 2155905152 = false := by decide +kernel

/-! Test (g) of the rule, multiplied out into whole numbers, with `integerSquareRoot (2^24) = 4,096`. -/
example : integerSquareRoot (2 ^ 24) = 4096 := by decide +kernel
example : (2 : Int) ^ (46 + 1) * (4096 + 1) + (2 ^ 39 + 4096 + 2) * 4096 + 2 ^ 32 * 4096
    ≤ 32639 * 2 ^ (32 + 1) * 4096 := by decide +kernel

/-! ## 3. A family of weights that pass -/

/-- A matrix whose entries pass `entriesWithin low high` is within every bound that covers
`low .. high`. -/
theorem matrixWithin_of_entriesWithin (low high bound : Int) (W : Matrix)
    (h : entriesWithin low high W = true) (lower : -bound ≤ low) (upper : high ≤ bound)
    (nonneg : 0 ≤ bound) : MatrixWithin bound W := by
  simp only [entriesWithin, Array.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have zero : magnitude 0 ≤ bound := by rw [magnitude_le_iff]; omega
  intro k j
  by_cases row : k < W.size
  · rw [entry_inside W k row]
    by_cases column : j < W[k].size
    · rw [entry_inside _ j column, magnitude_le_iff]
      have := h k row j column
      omega
    · rw [entry_outside _ j column]; exact zero
  · rw [entry_outside W k row, read_default]; exact zero

/-- **A family of weights that pass.** At any settings, take a number `entry` for which
`uniformCheck` passes (with the bounds 4,096 and 4,095 of the system's tables, and the bound of
`weightsInRange` on the embedding). Then all weights pass whose layers' matrices have every entry in
`-entry .. entry`. -/
theorem passesWorstCaseCheck_of_uniformCheck (settings : Settings)
    (weights : ModelWeights settings) (entry : Int)
    (small : ∀ l, l < settings.layers → LayerWithin entry (weights.val.perLayer.entry l))
    (passes : uniformCheck settings 4096 4095 entry 2155905152 = true) :
    PassesWorstCaseCheck settings weights := by
  have valid := weights.property
  simp only [weightsAreValid, weightsInRange, Bool.and_eq_true] at valid
  exact boxWorstCaseCheck_of_uniformCheck settings lookupTables weights.val 4096 4095 entry
    2155905152 cosineTable_within sineTable_within siluTable_within routedInputFits_lookupTables
    (matrixWithin_of_entriesWithin _ _ _ _ valid.2.1.1 (by decide) (by decide) (by decide))
    small passes

/-- **At the example settings all weights pass whose layers' matrices have every entry in
-256 .. 256**, whatever their embedding and their head matrix are. -/
theorem passesWorstCaseCheck_of_small_entries (weights : ModelWeights exampleSettings)
    (small : ∀ l, l < 48 → LayerWithin 256 (weights.val.perLayer.entry l)) :
    PassesWorstCaseCheck exampleSettings weights :=
  passesWorstCaseCheck_of_uniformCheck exampleSettings weights 256 small
    uniformCheck_exampleSettings

/-! ## 4. The family has a member in which no matrix is zero -/

/-- The matrix with the same number at every place. -/
def constantMatrix (rows columns : Nat) (value : Int) : Matrix :=
  tabulate rows fun _ => tabulate columns fun _ => value

/-- A gated block of constant matrices. -/
def constantGated (width hidden : Nat) (value : Int) : GatedWeights where
  gate := constantMatrix width hidden value
  up := constantMatrix width hidden value
  down := constantMatrix hidden width value

/-- A layer of constant matrices. A dense layer has no router and no routed experts. -/
def constantLayer (s : Settings) (value : Int) (mixture : Bool) : LayerWeights where
  query := constantMatrix s.width s.queryWidth value
  key := constantMatrix s.width s.keyValueWidth value
  value := constantMatrix s.width s.keyValueWidth value
  output := constantMatrix s.queryWidth s.width value
  shared := constantGated s.width (if mixture then s.expertHidden else s.hidden) value
  router := if mixture then constantMatrix s.width s.experts value else #[]
  routed := if mixture then tabulate s.experts fun _ => constantGated s.width s.expertHidden value
    else #[]

/-- Made-up weights: every entry of every matrix is `value`. -/
def constantWeights (s : Settings) (value : Int) : Weights where
  embedding := constantMatrix s.vocabulary s.width value
  perLayer := tabulate s.layers fun l => constantLayer s value (s.isMixture l)
  head := constantMatrix s.width s.vocabulary value

/-- A test that holds of every read inside an array holds of all its entries. -/
theorem all_of_reads {α : Type} [Inhabited α] (v : Array α) (test : α → Bool)
    (h : ∀ k, k < v.size → test (v.entry k) = true) : v.all test = true := by
  rw [Array.all_eq_true]
  intro k inside
  have := h k inside
  rwa [entry_inside v k inside] at this

/-- A matrix that is given entry by entry has its size. -/
theorem hasSize_tabulate (rows columns : Nat) (f : Nat → Nat → Int) :
    hasSize rows columns (tabulate rows fun k => tabulate columns fun j => f k j) = true := by
  simp only [hasSize, Bool.and_eq_true, beq_iff_eq]
  refine ⟨size_tabulate _ _, all_of_reads _ _ fun k inside => ?_⟩
  rw [size_tabulate] at inside
  rw [tabulate_read _ _ _ inside, size_tabulate]
  exact beq_self_eq_true _

/-- The entries of a constant matrix are in every interval that holds its number. -/
theorem entriesWithin_constantMatrix (rows columns : Nat) (value low high : Int)
    (lower : low ≤ value) (upper : value ≤ high) :
    entriesWithin low high (constantMatrix rows columns value) = true := by
  unfold entriesWithin constantMatrix
  refine all_of_reads _ _ fun k row => all_of_reads _ _ fun j column => ?_
  rw [size_tabulate] at row
  rw [tabulate_read _ _ _ row, size_tabulate] at column
  rw [tabulate_read _ _ _ row, tabulate_read _ _ _ column]
  simp [lower, upper]

/-- A constant matrix is within every bound on its number. -/
theorem matrixWithin_constantMatrix (rows columns : Nat) (value bound : Int)
    (h : magnitude value ≤ bound) : MatrixWithin bound (constantMatrix rows columns value) :=
  matrixWithin_tabulate _ _ _ _ (Int.le_trans (magnitude_nonneg _) h) fun _ _ => h

/-- A constant matrix has its size. -/
theorem hasSize_constantMatrix (rows columns : Nat) (value : Int) :
    hasSize rows columns (constantMatrix rows columns value) = true :=
  hasSize_tabulate _ _ _

/-- A gated block of constant matrices has its sizes. -/
theorem hasSizes_constantGated (width hidden : Nat) (value : Int) :
    (constantGated width hidden value).hasSizes width hidden = true := by
  simp only [GatedWeights.hasSizes, constantGated, hasSize_constantMatrix, Bool.and_self]

/-- The layers of the example settings. -/
theorem exampleSettings_layer (l : Nat) (h : l < 48) :
    exampleSettings.perLayer.entry l = exampleLayerSettings l :=
  tabulate_read 48 exampleLayerSettings l h

/-- The layers of the constant weights. -/
theorem constantWeights_layer (s : Settings) (value : Int) (l : Nat) (h : l < s.layers) :
    (constantWeights s value).perLayer.entry l = constantLayer s value (s.isMixture l) := by
  simp only [constantWeights]
  rw [tabulate_read _ _ _ h]

/-- At the example settings the odd layers are the mixture-of-experts layers. -/
theorem exampleSettings_isMixture (l : Nat) :
    exampleSettings.isMixture l = true ↔ l % 2 = 1 := by
  simp [Settings.isMixture, exampleSettings]

/-- A layer of constant matrices is well formed, if every `eps` and every shift that the layer hands
to `roundShift` is at least 1. -/
theorem layerWellFormed_constantLayer (s : Settings) (p : LayerSettings) (value : Int)
    (mixture : Bool) (eps1 : 1 ≤ p.attentionEps) (eps2 : 1 ≤ p.feedForwardEps)
    (shift1 : 1 ≤ p.attentionShift) (query : 1 ≤ p.queryShift) (key : 1 ≤ p.keyShift)
    (valueShift : 1 ≤ p.valueShift) (output : 1 ≤ p.outputShift)
    (shift2 : 1 ≤ p.feedForwardShift) (gate : 1 ≤ p.gateShift) (up : 1 ≤ p.upShift)
    (down : 1 ≤ p.downShift)
    (routed : mixture = true →
      1 ≤ p.routerShift ∧ 1 ≤ p.routedGateShift ∧ 1 ≤ p.routedUpShift) :
    layerWellFormed s p (constantLayer s value mixture) mixture = true := by
  simp only [layerWellFormed, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hasSize_constantMatrix _ _ _, hasSize_constantMatrix _ _ _⟩,
    hasSize_constantMatrix _ _ _⟩, hasSize_constantMatrix _ _ _⟩, eps1⟩, eps2⟩, shift1⟩, query⟩,
    key⟩, valueShift⟩, output⟩, shift2⟩, gate⟩, up⟩, down⟩, ?_⟩
  cases mixture with
  | false =>
    simp only [Bool.false_eq_true, if_false, constantLayer]
    exact hasSizes_constantGated _ _ _
  | true =>
    obtain ⟨router, routedGate, routedUp⟩ := routed rfl
    simp only [if_true, constantLayer, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨⟨hasSizes_constantGated _ _ _, hasSize_constantMatrix _ _ _⟩, size_tabulate _ _⟩,
      all_of_reads _ _ fun e inside => ?_⟩, router⟩, routedGate⟩, routedUp⟩
    rw [size_tabulate] at inside
    rw [tabulate_read _ _ _ inside]
    exact hasSizes_constantGated _ _ _

/-- A vector that is given entry by entry has no negative entry, if none is given. -/
theorem all_nonneg_tabulate (n : Nat) (f : Nat → Int) (h : ∀ k, 0 ≤ f k) :
    ((tabulate n f).all fun e => 0 ≤ e) = true := by
  refine all_of_reads _ _ fun k inside => ?_
  rw [size_tabulate] at inside
  rw [tabulate_read _ _ _ inside]
  simp only [decide_eq_true_eq]
  exact h k

/-- What `wellFormed` asks of the tables holds of the system's five tables, at 1,024 positions and
heads of 128 entries. -/
theorem lookupTables_wellFormed :
    hasSize 1024 64 lookupTables.cosine = true ∧ hasSize 1024 64 lookupTables.sine = true ∧
    0 < lookupTables.exponential.size ∧ 0 < lookupTables.exponential.entry 0 ∧
    (lookupTables.exponential.all fun e => 0 ≤ e) = true ∧
    lookupTables.silu.covers (-32768) 32767 = true ∧
    lookupTables.sigmoid.covers (-16384) 16383 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [lookupTables, cosineTable]; exact hasSize_tabulate _ _ _
  · simp only [lookupTables, sineTable]; exact hasSize_tabulate _ _ _
  · simp only [lookupTables, exponentialTable, size_tabulate]; decide
  · simp only [lookupTables, exponentialTable]
    rw [tabulate_read _ _ _ (by decide)]
    omega
  · have table : lookupTables.exponential = exponentialTable := by simp only [lookupTables]
    rw [table]
    unfold exponentialTable
    exact all_nonneg_tabulate _ _ fun k => by omega
  · simp only [KeyedTable.covers, lookupTables, siluTable, size_tabulate, Bool.and_eq_true,
      decide_eq_true_eq]
    decide
  · simp only [KeyedTable.covers, lookupTables, sigmoidTable, size_tabulate, Bool.and_eq_true,
      decide_eq_true_eq]
    decide

/-- The sizes of the embedding, of the head matrix and of the array of layers. -/
theorem constantWeights_sizes (s : Settings) (value : Int) :
    hasSize s.vocabulary s.width (constantWeights s value).embedding = true ∧
    hasSize s.width s.vocabulary (constantWeights s value).head = true ∧
    (constantWeights s value).perLayer.size = s.layers :=
  ⟨hasSize_constantMatrix _ _ _, hasSize_constantMatrix _ _ _, size_tabulate _ _⟩

/-- The entries of the embedding and of the head matrix. -/
theorem constantWeights_entries (s : Settings) (value low high : Int) (lower : low ≤ value)
    (upper : value ≤ high) :
    entriesWithin low high (constantWeights s value).embedding = true ∧
    entriesWithin low high (constantWeights s value).head = true :=
  ⟨entriesWithin_constantMatrix _ _ _ _ _ lower upper,
    entriesWithin_constantMatrix _ _ _ _ _ lower upper⟩

/-- The constant weights fit the example settings and the system's tables. -/
theorem wellFormed_constantWeights (value : Int) :
    wellFormed exampleSettings lookupTables (constantWeights exampleSettings value) = true := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := lookupTables_wellFormed
  obtain ⟨d1, d2, e2⟩ := constantWeights_sizes exampleSettings value
  simp only [wellFormed, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, by decide⟩, by decide⟩, by decide⟩, by decide⟩,
    Or.inr (by decide)⟩, by decide⟩, by decide⟩, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩,
    d1⟩, d2⟩, size_tabulate _ _⟩, e2⟩, fun l hl => ?_⟩
  rw [exampleSettings_layer l hl, constantWeights_layer _ _ l hl]
  apply layerWellFormed_constantLayer
  case routed =>
    intro mix
    have odd := (exampleSettings_isMixture l).mp mix
    simp [exampleLayerSettings, odd]
  all_goals simp [exampleLayerSettings]

/-- The matrices of a gated block of constant matrices contain weights of 13 bits. -/
theorem gatedWithin_constantGated (width hidden : Nat) (value : Int) (lower : -4096 ≤ value)
    (upper : value ≤ 4095) : gatedWithin (constantGated width hidden value) = true := by
  simp only [gatedWithin, constantGated, Bool.and_eq_true]
  exact ⟨⟨entriesWithin_constantMatrix _ _ _ _ _ lower upper,
    entriesWithin_constantMatrix _ _ _ _ _ lower upper⟩,
    entriesWithin_constantMatrix _ _ _ _ _ lower upper⟩

/-- The matrices of a layer of constant matrices contain weights of 13 bits. -/
theorem layerWeightsInRange_constantLayer (s : Settings) (value : Int) (mixture : Bool)
    (lower : -4096 ≤ value) (upper : value ≤ 4095) :
    layerWeightsInRange mixture (constantLayer s value mixture) = true := by
  simp only [layerWeightsInRange, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨entriesWithin_constantMatrix _ _ _ _ _ lower upper,
    entriesWithin_constantMatrix _ _ _ _ _ lower upper⟩,
    entriesWithin_constantMatrix _ _ _ _ _ lower upper⟩,
    entriesWithin_constantMatrix _ _ _ _ _ lower upper⟩,
    gatedWithin_constantGated _ _ _ lower upper⟩, ?_⟩
  cases mixture with
  | false => simp [constantLayer]
  | true =>
    simp only [if_true, constantLayer, Bool.and_eq_true]
    refine ⟨entriesWithin_constantMatrix _ _ _ _ _ lower upper,
      all_of_reads _ _ fun e inside => ?_⟩
    rw [size_tabulate] at inside
    rw [tabulate_read _ _ _ inside]
    exact gatedWithin_constantGated _ _ _ lower upper

/-- The constant weights are valid at the example settings, if their number has 13 bits. -/
theorem weightsAreValid_constantWeights (value : Int) (lower : -4096 ≤ value)
    (upper : value ≤ 4095) :
    weightsAreValid exampleSettings (constantWeights exampleSettings value) = true := by
  simp only [weightsAreValid, weightsInRange, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨wellFormed_constantWeights value,
    ⟨(constantWeights_entries exampleSettings value _ _ (by omega) (by omega)).1,
      (constantWeights_entries exampleSettings value _ _ lower upper).2⟩, fun l hl => ?_⟩
  rw [constantWeights_layer _ _ l hl]
  exact layerWeightsInRange_constantLayer _ _ _ lower upper

/-- The empty matrix is within every bound that is not negative. -/
theorem matrixWithin_empty (bound : Int) (nonneg : 0 ≤ bound) : MatrixWithin bound #[] := by
  intro k j
  show magnitude 0 ≤ bound
  rw [magnitude_le_iff]; omega

/-- A gated block of constant matrices is within every bound on its number. -/
theorem gatedWithin_bound_constantGated (width hidden : Nat) (value bound : Int)
    (h : magnitude value ≤ bound) : GatedWithin bound (constantGated width hidden value) :=
  ⟨matrixWithin_constantMatrix _ _ _ _ h, matrixWithin_constantMatrix _ _ _ _ h,
    matrixWithin_constantMatrix _ _ _ _ h⟩

/-- A layer of constant matrices is within every bound on its number. -/
theorem layerWithin_constantLayer (s : Settings) (value bound : Int) (mixture : Bool)
    (h : magnitude value ≤ bound) : LayerWithin bound (constantLayer s value mixture) := by
  have nonneg : 0 ≤ bound := Int.le_trans (magnitude_nonneg _) h
  have none : GatedWithin bound default :=
    ⟨matrixWithin_empty _ nonneg, matrixWithin_empty _ nonneg, matrixWithin_empty _ nonneg⟩
  refine ⟨matrixWithin_constantMatrix _ _ _ _ h, matrixWithin_constantMatrix _ _ _ _ h,
    matrixWithin_constantMatrix _ _ _ _ h, matrixWithin_constantMatrix _ _ _ _ h,
    gatedWithin_bound_constantGated _ _ _ _ h, ?_, fun e => ?_⟩
  · cases mixture with
    | false => exact matrixWithin_empty _ nonneg
    | true => exact matrixWithin_constantMatrix _ _ _ _ h
  · cases mixture with
    | false => exact none
    | true =>
      simp only [constantLayer, if_true]
      by_cases inside : e < s.experts
      · rw [tabulate_read _ _ _ inside]; exact gatedWithin_bound_constantGated _ _ _ _ h
      · rw [entry_outside _ e (by rw [size_tabulate]; exact inside)]; exact none

/-- Made-up weights at the example settings: every entry of every matrix is 256. -/
def constantModelWeights : ModelWeights exampleSettings :=
  ⟨constantWeights exampleSettings 256,
    weightsAreValid_constantWeights 256 (by decide) (by decide)⟩

/-- **Some weights pass**: the made-up weights with 256 at every place of every matrix. -/
theorem passesWorstCaseCheck_constantModelWeights :
    PassesWorstCaseCheck exampleSettings constantModelWeights := by
  apply passesWorstCaseCheck_of_small_entries
  intro l hl
  show LayerWithin 256 ((constantWeights exampleSettings 256).perLayer.entry l)
  rw [constantWeights_layer _ _ l hl]
  exact layerWithin_constantLayer _ _ _ _ (by decide)

/-- So at these weights the model never fails. -/
theorem modelNeverFails_constantModelWeights :
    ModelNeverFails exampleSettings constantModelWeights :=
  modelNeverFails_of_passesWorstCaseCheck _ _ passesWorstCaseCheck_constantModelWeights

end VerifiableInference.Bounds

#print axioms VerifiableInference.Bounds.passesWorstCaseCheck_of_uniformCheck
#print axioms VerifiableInference.Bounds.passesWorstCaseCheck_of_small_entries
#print axioms VerifiableInference.Bounds.passesWorstCaseCheck_constantModelWeights
#print axioms VerifiableInference.Bounds.modelNeverFails_constantModelWeights
