-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Bounds.Attention
import IntegerModel.Bounds.Lengths

/-!
# A test on a few numbers that is enough for the worst-case check

`uniformCheck settings rotary silu entry embedding` reads the settings and four numbers, and no
array of weights: `entry` stands for the largest absolute value of an entry of any weight matrix of
a layer, `embedding` for that of the embedding, `rotary` and `silu` for those of the rotary tables
and of the SiLU table. It is `boxWorstCaseCheck` (IntegerModel/Bounds/Check.lean) with every
column's sum replaced by the number of rows times the largest entry.

`boxWorstCaseCheck_of_uniformCheck`: if the four numbers bound what they stand for and
`uniformCheck` passes, then `boxWorstCaseCheck` passes. So a whole family of weights, given by one
bound on their entries, can be shown to pass without evaluating a sum over a matrix.

Limit: the test is much coarser than `boxWorstCaseCheck`. Only Lean's core library is used.
-/

namespace IntegerTransformer.Bounds

/-! ## Definitions -/

/-- Every read of the matrix, inside or outside, is at most `bound` in absolute value. -/
def MatrixWithin (bound : Int) (W : Matrix) : Prop :=
  ∀ k j, magnitude ((W.entry k).entry j) ≤ bound

/-- The three matrices of a gated block are within `bound`. -/
def GatedWithin (bound : Int) (w : GatedWeights) : Prop :=
  MatrixWithin bound w.gate ∧ MatrixWithin bound w.up ∧ MatrixWithin bound w.down

/-- All matrices of a layer are within `bound`. -/
def LayerWithin (bound : Int) (w : LayerWeights) : Prop :=
  MatrixWithin bound w.query ∧ MatrixWithin bound w.key ∧ MatrixWithin bound w.value ∧
    MatrixWithin bound w.output ∧ GatedWithin bound w.shared ∧ MatrixWithin bound w.router ∧
    ∀ e, GatedWithin bound (w.routed.entry e)

/-- Bounds `columnBound`: the number of rows times the input's bound times the entries' bound. -/
def uniformColumnBound (inputBound : Int) (rows : Nat) (entry : Int) : Int :=
  rows * (inputBound * entry)

/-- Bounds `upBound`. -/
def uniformUpBound (width : Nat) (entry : Int) (upShift : Nat) : Int :=
  roundShift (uniformColumnBound activationBound width entry) upShift

/-- Bounds `downBound`. -/
def uniformDownBound (width hidden : Nat) (silu entry : Int) (upShift : Nat) : Int :=
  uniformColumnBound (silu * uniformUpBound width entry upShift) hidden entry

/-- Bounds `attentionAdditionBound`. -/
def uniformAttentionAddition (s : Settings) (p : LayerSettings) (entry : Int) : Int :=
  roundShift (uniformColumnBound activationBound s.queryWidth entry) p.outputShift

/-- Bounds `feedForwardAdditionBound`. -/
def uniformFeedForwardAddition (s : Settings) (p : LayerSettings) (silu entry : Int)
    (mixture : Bool) : Int :=
  if mixture then
    roundShift (uniformDownBound s.width s.expertHidden silu entry p.upShift +
      uniformDownBound s.width s.expertHidden silu entry p.routedUpShift) p.downShift
  else roundShift (uniformDownBound s.width s.hidden silu entry p.upShift) p.downShift

/-- Bounds `layerAdditionBound`. -/
def uniformLayerAddition (s : Settings) (silu entry : Int) (l : Nat) : Int :=
  uniformAttentionAddition s (s.perLayer.entry l) entry +
    uniformFeedForwardAddition s (s.perLayer.entry l) silu entry (s.isMixture l)

/-- Bounds `streamBound`, at every coordinate. -/
def uniformStreamBound (s : Settings) (silu entry embedding : Int) (l : Nat) : Int :=
  embedding + sumOver l fun below => uniformLayerAddition s silu entry below

/-- Enough for `normFits` at a row with every coordinate within `bound`. -/
def uniformNormFits (bits shift : Nat) (eps : Int) (width : Nat) (bound : Int) : Bool :=
  let sumSquaresBound : Int := width * (bound * bound)
  let rootBound : Int := integerSquareRoot (sumSquaresBound + eps).toNat
  sumSquaresBound + eps < 2 ^ 78
  && roundShift (2 ^ bits + rootBound / 2) shift ≤ 32767

/-- Enough for `unitsFit`. -/
def uniformUnitsFit (width : Nat) (entry : Int) (gateShift upShift : Nat) : Bool :=
  roundShift (uniformColumnBound activationBound width entry) gateShift ≤ 4194175
  && uniformUpBound width entry upShift ≤ 32767

/-- Enough for `layerFits`. -/
def uniformLayerFits (s : Settings) (rotary silu entry embedding : Int) (l : Nat) : Bool :=
  let p := s.perLayer.entry l
  let product := uniformColumnBound activationBound s.width entry
  uniformNormFits p.attentionBits p.attentionShift p.attentionEps s.width
    (uniformStreamBound s silu entry embedding l)
  && roundShift (rotary * product + rotary * product) p.queryShift ≤ 32767
  && roundShift (rotary * product + rotary * product) p.keyShift ≤ 32767
  && roundShift product p.valueShift ≤ 32767
  && uniformNormFits p.feedForwardBits p.feedForwardShift p.feedForwardEps s.width
    (uniformStreamBound s silu entry embedding l + uniformAttentionAddition s p entry)
  && uniformUnitsFit s.width entry p.gateShift p.upShift
  && (!s.isMixture l ||
    (roundShift product p.routerShift ≤ 262143
      && uniformUnitsFit s.width entry p.routedGateShift p.routedUpShift))

/-- The test on the settings and four numbers. -/
def uniformCheck (s : Settings) (rotary silu entry embedding : Int) : Bool :=
  0 ≤ entry && 0 ≤ embedding && 0 ≤ silu && 2 ^ s.rotaryScale ≤ rotary
  && (allBelow s.layers fun l => uniformLayerFits s rotary silu entry embedding l)
  && uniformNormFits s.finalBits s.finalShift s.finalEps s.width
    (uniformStreamBound s silu entry embedding s.layers)

/-! ## Each bound of the check is at most its uniform bound -/

/-- Sums of equal terms are equal. -/
theorem sumOver_congr (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k = g k) :
    sumOver n f = sumOver n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumOver]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

/-- For `b ≥ 0`, `roundShift b k` is not negative. -/
theorem roundShift_nonneg (b : Int) (k : Nat) (h : 0 ≤ b) : 0 ≤ roundShift b k := by
  have bound := magnitude_roundShift_le 0 b k (by rw [magnitude_le_iff]; omega)
  have := magnitude_nonneg (roundShift 0 k)
  omega

/-- `columnBound` is not negative, if the input's bounds are not. -/
theorem columnBound_nonneg (inputBound : Nat → Int) (W : Matrix) (rows column : Nat)
    (h : ∀ k, 0 ≤ inputBound k) : 0 ≤ columnBound inputBound W rows column :=
  sumOver_nonneg _ (fun k => Int.mul_nonneg (h k) (magnitude_nonneg _)) _

/-- `columnBound` is at most its uniform bound. -/
theorem columnBound_le (inputBound : Nat → Int) (W : Matrix) (rows column : Nat) (B entry : Int)
    (nonneg : ∀ k, 0 ≤ inputBound k) (le : ∀ k, inputBound k ≤ B) (within : MatrixWithin entry W) :
    columnBound inputBound W rows column ≤ uniformColumnBound B rows entry := by
  unfold columnBound uniformColumnBound
  rw [← sumOver_const]
  apply sumOver_le_sumOver
  intro k _
  exact Int.mul_le_mul (le k) (within k column) (magnitude_nonneg _)
    (Int.le_trans (nonneg k) (le k))

/-- `boxColumnBound` is at most its uniform bound. -/
theorem boxColumnBound_le (W : Matrix) (rows column : Nat) (entry : Int)
    (within : MatrixWithin entry W) :
    boxColumnBound W rows column ≤ uniformColumnBound activationBound rows entry :=
  columnBound_le _ W rows column activationBound entry (fun _ => by decide)
    (fun _ => Int.le_refl _) within

/-- `largestMagnitude` is not negative. -/
theorem largestMagnitude_nonneg (v : IntegerVector) : 0 ≤ largestMagnitude v :=
  Int.le_trans (magnitude_nonneg _) (magnitude_entry_le_largestMagnitude v 0)

/-- `maxUpTo f i` is at most a number that none of `f 0, .., f i` exceeds. -/
theorem maxUpTo_le (f : Nat → Int) (i : Nat) (b : Int) (h : ∀ j, j ≤ i → f j ≤ b) :
    maxUpTo f i ≤ b := by
  obtain ⟨j, hj, attained⟩ := (maxUpTo_spec f i).2
  rw [← attained]
  exact h j hj

/-- `upBound` is not negative. -/
theorem upBound_nonneg (w : GatedWeights) (width upShift j : Nat) : 0 ≤ upBound w width upShift j :=
  roundShift_nonneg _ _ (boxColumnBound_nonneg _ _ _)

/-- `upBound` is at most its uniform bound. -/
theorem upBound_le (w : GatedWeights) (width upShift j : Nat) (entry : Int)
    (within : MatrixWithin entry w.up) :
    upBound w width upShift j ≤ uniformUpBound width entry upShift :=
  roundShift_le_roundShift _ _ _ (boxColumnBound_le _ _ _ _ within)

/-- `downBound` is not negative. -/
theorem downBound_nonneg (tables : Tables) (w : GatedWeights) (width hidden upShift k : Nat) :
    0 ≤ downBound tables w width hidden upShift k :=
  columnBound_nonneg _ _ _ _
    fun _ => Int.mul_nonneg (largestMagnitude_nonneg _) (upBound_nonneg _ _ _ _)

/-- `downBound` is at most its uniform bound. -/
theorem downBound_le (tables : Tables) (w : GatedWeights) (width hidden upShift k : Nat)
    (silu entry : Int) (siluWithin : largestMagnitude tables.silu.entries ≤ silu)
    (within : GatedWithin entry w) :
    downBound tables w width hidden upShift k ≤
      uniformDownBound width hidden silu entry upShift := by
  unfold downBound uniformDownBound
  apply columnBound_le _ _ _ _ _ _ _ _ within.2.2
  · exact fun _ => Int.mul_nonneg (largestMagnitude_nonneg _) (upBound_nonneg _ _ _ _)
  · exact fun j => Int.mul_le_mul siluWithin (upBound_le w width upShift j entry within.2.1)
      (upBound_nonneg _ _ _ _) (Int.le_trans (largestMagnitude_nonneg _) siluWithin)

/-- `attentionAdditionBound` is not negative and at most its uniform bound. -/
theorem attentionAdditionBound_le (s : Settings) (p : LayerSettings) (w : LayerWeights) (k : Nat)
    (entry : Int) (within : LayerWithin entry w) :
    0 ≤ attentionAdditionBound s p w k ∧
      attentionAdditionBound s p w k ≤ uniformAttentionAddition s p entry :=
  ⟨roundShift_nonneg _ _ (boxColumnBound_nonneg _ _ _),
    roundShift_le_roundShift _ _ _ (boxColumnBound_le _ _ _ _ within.2.2.2.1)⟩

/-- `feedForwardAdditionBound` is not negative and at most its uniform bound. -/
theorem feedForwardAdditionBound_le (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (mixture : Bool) (k : Nat) (silu entry : Int)
    (siluWithin : largestMagnitude tables.silu.entries ≤ silu) (within : LayerWithin entry w) :
    0 ≤ feedForwardAdditionBound s p tables w mixture k ∧
      feedForwardAdditionBound s p tables w mixture k ≤
        uniformFeedForwardAddition s p silu entry mixture := by
  have shared := within.2.2.2.2.1
  have routed := within.2.2.2.2.2.2
  cases mixture with
  | false =>
    simp only [feedForwardAdditionBound, uniformFeedForwardAddition, Bool.false_eq_true, if_false]
    exact ⟨roundShift_nonneg _ _ (downBound_nonneg _ _ _ _ _ _),
      roundShift_le_roundShift _ _ _ (downBound_le _ _ _ _ _ _ _ _ siluWithin shared)⟩
  | true =>
    simp only [feedForwardAdditionBound, uniformFeedForwardAddition, if_true]
    have first := (maxUpTo_spec (fun e => downBound tables (w.routed.entry e) s.width
      s.expertHidden p.routedUpShift k) (s.experts - 1)).1 0 (by omega)
    have zero := downBound_nonneg tables (w.routed.entry 0) s.width s.expertHidden
      p.routedUpShift k
    have one := downBound_nonneg tables w.shared s.width s.expertHidden p.upShift k
    constructor
    · apply roundShift_nonneg
      simp only at first
      omega
    · apply roundShift_le_roundShift
      apply Int.add_le_add (downBound_le _ _ _ _ _ _ _ _ siluWithin shared)
      exact maxUpTo_le _ _ _ fun e _ => downBound_le _ _ _ _ _ _ _ _ siluWithin (routed e)

/-- `streamBound` is not negative and at most its uniform bound, up to the last layer. -/
theorem streamBound_le (s : Settings) (tables : Tables) (weights : Weights)
    (silu entry embedding : Int) (siluWithin : largestMagnitude tables.silu.entries ≤ silu)
    (embeddingWithin : MatrixWithin embedding weights.embedding)
    (layersWithin : ∀ l, l < s.layers → LayerWithin entry (weights.perLayer.entry l))
    (l k : Nat) (hl : l ≤ s.layers) :
    0 ≤ streamBound s tables weights l k ∧
      streamBound s tables weights l k ≤ uniformStreamBound s silu entry embedding l := by
  have parts : ∀ below, below < l →
      0 ≤ layerAdditionBound s tables weights below k ∧
        layerAdditionBound s tables weights below k ≤ uniformLayerAddition s silu entry below := by
    intro below h
    have a := attentionAdditionBound_le s (s.perLayer.entry below) (weights.perLayer.entry below) k
      entry (layersWithin below (by omega))
    have f := feedForwardAdditionBound_le s (s.perLayer.entry below) tables
      (weights.perLayer.entry below) (s.isMixture below) k silu entry siluWithin
      (layersWithin below (by omega))
    unfold layerAdditionBound uniformLayerAddition
    omega
  have low : 0 ≤ embeddingBound s weights k :=
    Int.le_trans (magnitude_nonneg _) ((maxUpTo_spec (fun token =>
      magnitude ((weights.embedding.entry token).entry k)) (s.vocabulary - 1)).1 0 (by omega))
  have high : embeddingBound s weights k ≤ embedding :=
    maxUpTo_le _ _ _ fun token _ => embeddingWithin token k
  have sumLow : sumOver l (fun _ => (0 : Int)) ≤
      sumOver l fun below => layerAdditionBound s tables weights below k :=
    sumOver_le_sumOver _ _ _ fun below h => (parts below h).1
  have sumHigh := sumOver_le_sumOver l
    (fun below => layerAdditionBound s tables weights below k)
    (fun below => uniformLayerAddition s silu entry below) fun below h => (parts below h).2
  rw [sumOver_const, Int.mul_zero] at sumLow
  unfold streamBound uniformStreamBound
  omega

/-- `integerSquareRoot a ≤ r`, if `a` is below the square of `r + 1`. -/
theorem isqrt_le_of_lt_square (a r : Nat) (h : a < (r + 1) * (r + 1)) : integerSquareRoot a ≤ r := by
  apply Nat.le_of_not_gt
  intro bad
  have low := (isqrt_spec a).1
  have : (r + 1) * (r + 1) ≤ integerSquareRoot a * integerSquareRoot a := Nat.mul_le_mul bad bad
  omega

/-- `normFits` passes, if `uniformNormFits` does for a number that bounds every coordinate's bound.
-/
theorem normFits_of_uniformNormFits (bits shift : Nat) (eps : Int) (width : Nat)
    (bound : Nat → Int) (B : Int) (nonneg : ∀ k, 0 ≤ bound k) (le : ∀ k, bound k ≤ B)
    (fits : uniformNormFits bits shift eps width B = true) :
    normFits bits shift eps width bound = true := by
  simp only [uniformNormFits, Bool.and_eq_true, decide_eq_true_eq] at fits
  have sum : (sumOver width fun k => bound k * bound k) ≤ width * (B * B) := by
    rw [← sumOver_const]
    exact sumOver_le_sumOver _ _ _ fun k _ =>
      Int.mul_le_mul (le k) (le k) (nonneg k) (Int.le_trans (nonneg k) (le k))
  simp only [normFits, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, Int.le_trans (roundShift_le_roundShift _ _ _ ?_) fits.2⟩
  have root := isqrt_le_isqrt ((sumOver width fun k => bound k * bound k) + eps).toNat
    (width * (B * B) + eps).toNat (by omega)
  omega

/-! ## Each test of the check follows from its uniform test -/

/-- Every read of the row of cosines is within the rotary tables' bound. -/
theorem cosineRow_le (s : Settings) (p : LayerSettings) (tables : Tables) (t i : Nat) (rotary : Int)
    (cosines : MatrixWithin rotary tables.cosine) (scale : 2 ^ s.rotaryScale ≤ rotary) :
    magnitude ((cosineRow s p tables t).entry i) ≤ rotary := by
  have positive : (0 : Int) < 2 ^ s.rotaryScale := Int.pow_pos (by decide)
  unfold cosineRow
  split
  · exact cosines t i
  · by_cases inside : i < s.headDim / 2
    · rw [tabulate_read _ _ _ inside, magnitude_le_iff]; omega
    · rw [entry_outside _ i (by rw [size_tabulate]; exact inside)]
      show magnitude 0 ≤ rotary
      rw [magnitude_le_iff]; omega

/-- Every read of the row of sines is within the rotary tables' bound. -/
theorem sineRow_le (s : Settings) (p : LayerSettings) (tables : Tables) (t i : Nat) (rotary : Int)
    (sines : MatrixWithin rotary tables.sine) (nonneg : 0 ≤ rotary) :
    magnitude ((sineRow s p tables t).entry i) ≤ rotary := by
  unfold sineRow
  split
  · exact sines t i
  · by_cases inside : i < s.headDim / 2
    · rw [tabulate_read _ _ _ inside, magnitude_le_iff]; omega
    · rw [entry_outside _ i (by rw [size_tabulate]; exact inside)]
      show magnitude 0 ≤ rotary
      rw [magnitude_le_iff]; omega

/-- `rotatedBound` is at most its uniform bound. -/
theorem rotatedBound_le (cosine sine : IntegerVector) (headDim : Nat) (productBound : Nat → Int) (j : Nat)
    (rotary B : Int) (cosines : ∀ i, magnitude (cosine.entry i) ≤ rotary)
    (sines : ∀ i, magnitude (sine.entry i) ≤ rotary) (nonneg : ∀ j, 0 ≤ productBound j)
    (le : ∀ j, productBound j ≤ B) :
    rotatedBound cosine sine headDim productBound j ≤ rotary * B + rotary * B := by
  have positive : 0 ≤ rotary := Int.le_trans (magnitude_nonneg _) (cosines 0)
  unfold rotatedBound
  dsimp only
  split
  · exact Int.add_le_add (Int.mul_le_mul (cosines _) (le _) (nonneg _) positive)
      (Int.mul_le_mul (sines _) (le _) (nonneg _) positive)
  · exact Int.add_le_add (Int.mul_le_mul (sines _) (le _) (nonneg _) positive)
      (Int.mul_le_mul (cosines _) (le _) (nonneg _) positive)

/-- `attentionFits` passes, if the three uniform tests do. -/
theorem attentionFits_of_uniform (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (rotary entry : Int) (cosines : MatrixWithin rotary tables.cosine)
    (sines : MatrixWithin rotary tables.sine) (scale : 2 ^ s.rotaryScale ≤ rotary)
    (within : LayerWithin entry w)
    (query : roundShift (rotary * uniformColumnBound activationBound s.width entry +
      rotary * uniformColumnBound activationBound s.width entry) p.queryShift ≤ 32767)
    (key : roundShift (rotary * uniformColumnBound activationBound s.width entry +
      rotary * uniformColumnBound activationBound s.width entry) p.keyShift ≤ 32767)
    (value : roundShift (uniformColumnBound activationBound s.width entry) p.valueShift ≤ 32767) :
    attentionFits s p tables w = true := by
  have positive : (0 : Int) < 2 ^ s.rotaryScale := Int.pow_pos (by decide)
  simp only [attentionFits, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq]
  refine ⟨fun t _ => ⟨fun j _ => ?_, fun j _ => ?_⟩, fun j _ => ?_⟩
  · exact Int.le_trans (roundShift_le_roundShift _ _ _ (rotatedBound_le _ _ _ _ _ rotary _
      (fun i => cosineRow_le s p tables t i rotary cosines scale)
      (fun i => sineRow_le s p tables t i rotary sines (by omega))
      (fun j => boxColumnBound_nonneg _ _ j)
      (fun j => boxColumnBound_le _ _ j entry within.1))) query
  · exact Int.le_trans (roundShift_le_roundShift _ _ _ (rotatedBound_le _ _ _ _ _ rotary _
      (fun i => cosineRow_le s p tables t i rotary cosines scale)
      (fun i => sineRow_le s p tables t i rotary sines (by omega))
      (fun j => boxColumnBound_nonneg _ _ j)
      (fun j => boxColumnBound_le _ _ j entry within.2.1))) key
  · exact Int.le_trans (roundShift_le_roundShift _ _ _
      (boxColumnBound_le _ _ j entry within.2.2.1)) value

/-- `unitsFit` passes, if `uniformUnitsFit` does. -/
theorem unitsFit_of_uniformUnitsFit (w : GatedWeights) (width hidden gateShift upShift : Nat)
    (entry : Int) (within : GatedWithin entry w)
    (fits : uniformUnitsFit width entry gateShift upShift = true) :
    unitsFit w width hidden gateShift upShift = true := by
  simp only [uniformUnitsFit, Bool.and_eq_true, decide_eq_true_eq] at fits
  simp only [unitsFit, allBelow_spec, Bool.and_eq_true, decide_eq_true_eq]
  exact fun j _ => ⟨Int.le_trans (roundShift_le_roundShift _ _ _
    (boxColumnBound_le _ _ j entry within.1)) fits.1,
    Int.le_trans (upBound_le w width upShift j entry within.2.1) fits.2⟩

/-- `feedForwardFits` passes, if the uniform tests do. -/
theorem feedForwardFits_of_uniform (s : Settings) (p : LayerSettings) (w : LayerWeights)
    (mixture : Bool) (entry : Int) (within : LayerWithin entry w)
    (shared : uniformUnitsFit s.width entry p.gateShift p.upShift = true)
    (routed : mixture = false ∨
      (roundShift (uniformColumnBound activationBound s.width entry) p.routerShift ≤ 262143 ∧
        uniformUnitsFit s.width entry p.routedGateShift p.routedUpShift = true)) :
    feedForwardFits s p w mixture = true := by
  cases mixture with
  | false =>
    simp only [feedForwardFits, Bool.false_eq_true, if_false]
    exact unitsFit_of_uniformUnitsFit _ _ _ _ _ entry within.2.2.2.2.1 shared
  | true =>
    rcases routed with impossible | routed
    · exact absurd impossible (by decide)
    · simp only [feedForwardFits, if_true, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq]
      exact ⟨unitsFit_of_uniformUnitsFit _ _ _ _ _ entry within.2.2.2.2.1 shared,
        fun e _ => ⟨Int.le_trans (roundShift_le_roundShift _ _ _
          (boxColumnBound_le _ _ e entry within.2.2.2.2.2.1)) routed.1,
          unitsFit_of_uniformUnitsFit _ _ _ _ _ entry (within.2.2.2.2.2.2 e) routed.2⟩⟩

/-- **If the four numbers bound what they stand for and `uniformCheck` passes, the worst-case check
passes.** -/
theorem boxWorstCaseCheck_of_uniformCheck (s : Settings) (tables : Tables) (weights : Weights)
    (rotary silu entry embedding : Int)
    (cosines : MatrixWithin rotary tables.cosine) (sines : MatrixWithin rotary tables.sine)
    (siluWithin : largestMagnitude tables.silu.entries ≤ silu)
    (routedFit : routedInputFits tables = true)
    (embeddingWithin : MatrixWithin embedding weights.embedding)
    (layersWithin : ∀ l, l < s.layers → LayerWithin entry (weights.perLayer.entry l))
    (passes : uniformCheck s rotary silu entry embedding = true) :
    boxWorstCaseCheck s tables weights = true := by
  simp only [uniformCheck, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq] at passes
  obtain ⟨⟨⟨_, scale⟩, layers⟩, final⟩ := passes
  have stream := streamBound_le s tables weights silu entry embedding siluWithin embeddingWithin
    layersWithin
  simp only [boxWorstCaseCheck, Bool.and_eq_true, allBelow_spec]
  refine ⟨⟨routedFit, fun l hl => ?_⟩, ?_⟩
  · have fits := layers l hl
    simp only [uniformLayerFits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at fits
    obtain ⟨⟨⟨⟨⟨⟨norm1, query⟩, key⟩, value⟩, norm2⟩, shared⟩, routed⟩ := fits
    have within := layersWithin l hl
    simp only [layerFits, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact normFits_of_uniformNormFits _ _ _ _ _ _ (fun k => (stream l k (by omega)).1)
        (fun k => (stream l k (by omega)).2) norm1
    · exact attentionFits_of_uniform s _ tables _ rotary entry cosines sines scale within query
        key value
    · apply normFits_of_uniformNormFits _ _ _ _ _ _ _ _ norm2
      · intro k
        have := (stream l k (by omega)).1
        have := (attentionAdditionBound_le s (s.perLayer.entry l) (weights.perLayer.entry l) k
          entry within).1
        unfold streamBoundAfterAttention
        omega
      · intro k
        have := (stream l k (by omega)).2
        have := (attentionAdditionBound_le s (s.perLayer.entry l) (weights.perLayer.entry l) k
          entry within).2
        unfold streamBoundAfterAttention
        omega
    · exact feedForwardFits_of_uniform s _ _ _ entry within shared routed
  · exact normFits_of_uniformNormFits _ _ _ _ _ _ (fun k => (stream s.layers k (by omega)).1)
      (fun k => (stream s.layers k (by omega)).2) final

end IntegerTransformer.Bounds
