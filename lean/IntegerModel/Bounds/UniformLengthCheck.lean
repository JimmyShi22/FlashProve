-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/UniformLengthCheck.lean

A test on a few numbers that is enough for the length check.

`uniformLengthCheck settings rotary silu entry embedding bound` reads the settings, four numbers
and, for each layer, five numbers `bound`, which stand for the largest of the given stretch numbers.
It reads no array of weights. As in IntegerModel/Bounds/UniformCheck.lean, `entry` stands for the
largest absolute value of an entry of any weight matrix of a layer, `embedding` for that of the
embedding, `rotary` and `silu` for those of the rotary tables and of the SiLU table. It follows
`lengthWorstCaseCheck` (IntegerModel/Bounds/LengthCheck.lean), with these differences:
- every column's sum of absolute values or of squares is replaced by the number of rows times the
  largest entry or its square, and the stretch numbers by `bound`;
- for the bound after the rotary step it has
  `rotary * attentionColumnBound + rotary * attentionColumnBound`, one number for all positions and
  columns;
- for the largest bound over the routed experts it has one number;
- it leaves `routedInputFits` out, which is a premise of its own in the theorem below;
- it adds four tests on its own arguments: three are not negative, and `rotary` is at least
  `2 ^ rotaryScale`.

- `lengthWorstCaseCheck_of_uniformLengthCheck`: if the four numbers bound what they stand for, the
  stretch numbers are within `bound`, the tables pass `routedInputFits` and `uniformLengthCheck`
  passes, then `lengthWorstCaseCheck` passes with these stretch numbers.
- `frobeniusStretchNumbers_within`: the Frobenius stretch numbers are within the numbers of
  `uniformFrobeniusStretch`.

The proofs show that every bound of the check does not fall when a column's sums, the embedding's
length, the table's largest entry, a stretch or a row's length grows.

Limit: the test is much coarser than `lengthWorstCaseCheck`. Only Lean's core library is used.
-/
import IntegerModel.Bounds.UniformCheck
import IntegerModel.Bounds.LengthNeverFails

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-! ## Definitions -/

/-- One number for each layer and each kind of matrix that the check treats by lengths. -/
structure UniformStretch where
  output : Nat → Int
  up : Nat → Int
  down : Nat → Int
  routedUp : Nat → Int
  routedDown : Nat → Int

/-- No stretch number is negative, and each is at most the number for its layer and kind. For the
routed experts' numbers this is asked at every index, in dense layers too, whether the check reads
the number or not. -/
def StretchNumbersWithin (settings : Settings) (numbers : StretchNumbers)
    (bound : UniformStretch) : Prop :=
  ∀ layer, layer < settings.layers →
    (0 ≤ numbers.output layer ∧ numbers.output layer ≤ bound.output layer)
    ∧ (0 ≤ numbers.up layer ∧ numbers.up layer ≤ bound.up layer)
    ∧ (0 ≤ numbers.down layer ∧ numbers.down layer ≤ bound.down layer)
    ∧ ∀ expert,
      (0 ≤ numbers.routedUp layer expert ∧ numbers.routedUp layer expert ≤ bound.routedUp layer)
      ∧ (0 ≤ numbers.routedDown layer expert
        ∧ numbers.routedDown layer expert ≤ bound.routedDown layer)

/-- Bounds `columnBoundInBall`: a column of `rows` entries within `entry`. -/
def uniformColumnBoundInBall (radius : Int) (rows : Nat) (entry : Int) : Int :=
  min (uniformColumnBound activationBound rows entry)
    (integerSquareRoot (radius * radius * (rows * (entry * entry))).toNat)

/-- Bounds `frobeniusStretch`. -/
def uniformFrobenius (rows columns : Nat) (entry : Int) : Int :=
  rootUp (columns * (rows * (entry * entry)))

/-- Bounds `hiddenLength`. -/
def uniformHiddenLength (silu : Int) (hidden upShift : Nat) (stretchUp radius : Int) : Int :=
  silu * roundedLength hidden (stretchUp * radius) upShift

/-- Bounds `feedForwardAdditionLength`. -/
def uniformFeedForwardAdditionLength (settings : Settings) (silu : Int) (bound : UniformStretch)
    (layer : Nat) (radius : Int) : Int :=
  let layerSettings := settings.perLayer.entry layer
  if settings.isMixture layer then
    roundedLength settings.width
      (bound.down layer
          * uniformHiddenLength silu settings.expertHidden layerSettings.upShift (bound.up layer)
            radius
        + bound.routedDown layer
          * uniformHiddenLength silu settings.expertHidden layerSettings.routedUpShift
            (bound.routedUp layer) radius)
      layerSettings.downShift
  else
    roundedLength settings.width
      (bound.down layer
        * uniformHiddenLength silu settings.hidden layerSettings.upShift (bound.up layer) radius)
      layerSettings.downShift

/-- Bounds `streamLength`. -/
def uniformStreamLength (settings : Settings) (silu embedding : Int) (bound : UniformStretch) :
    Nat → Int
  | 0 => rootUp (settings.width * (embedding * embedding))
  | layer + 1 =>
    let between := uniformStreamLength settings silu embedding bound layer
      + attentionAdditionLength settings (settings.perLayer.entry layer) (bound.output layer)
    between + uniformFeedForwardAdditionLength settings silu bound layer
      (feedForwardRadius settings layer between)

/-- Enough for `unitsFitInBall`. -/
def uniformUnitsFitInBall (width : Nat) (entry : Int) (gateShift upShift : Nat) (radius : Int) :
    Bool :=
  roundShift (uniformColumnBoundInBall radius width entry) gateShift ≤ 4194175
  && roundShift (uniformColumnBoundInBall radius width entry) upShift ≤ 32767

/-- Enough for `lengthLayerFits`. -/
def uniformLengthLayerFits (settings : Settings) (rotary silu entry embedding : Int)
    (bound : UniformStretch) (layer : Nat) : Bool :=
  let layerSettings := settings.perLayer.entry layer
  let entering := uniformStreamLength settings silu embedding bound layer
  let between := entering + attentionAdditionLength settings layerSettings (bound.output layer)
  let attentionColumnBound := uniformColumnBoundInBall
    (ballRadius settings.width layerSettings.attentionBits layerSettings.attentionShift
      layerSettings.attentionEps entering)
    settings.width entry
  let secondRadius := feedForwardRadius settings layer between
  normFitsLength layerSettings.attentionBits layerSettings.attentionShift
      layerSettings.attentionEps entering
  && roundShift (rotary * attentionColumnBound + rotary * attentionColumnBound)
      layerSettings.queryShift ≤ 32767
  && roundShift (rotary * attentionColumnBound + rotary * attentionColumnBound)
      layerSettings.keyShift ≤ 32767
  && roundShift attentionColumnBound layerSettings.valueShift ≤ 32767
  && normFitsLength layerSettings.feedForwardBits layerSettings.feedForwardShift
      layerSettings.feedForwardEps between
  && uniformUnitsFitInBall settings.width entry layerSettings.gateShift layerSettings.upShift
      secondRadius
  && (!settings.isMixture layer ||
    (roundShift (uniformColumnBoundInBall secondRadius settings.width entry)
        layerSettings.routerShift ≤ 262143
      && uniformUnitsFitInBall settings.width entry layerSettings.routedGateShift
        layerSettings.routedUpShift secondRadius))

/-- The test on the settings, four numbers and the numbers `bound` for the stretch numbers. -/
def uniformLengthCheck (settings : Settings) (rotary silu entry embedding : Int)
    (bound : UniformStretch) : Bool :=
  0 ≤ entry && 0 ≤ embedding && 0 ≤ silu && 2 ^ settings.rotaryScale ≤ rotary
  && (allBelow settings.layers fun layer =>
    uniformLengthLayerFits settings rotary silu entry embedding bound layer)
  && normFitsLength settings.finalBits settings.finalShift settings.finalEps
    (uniformStreamLength settings silu embedding bound settings.layers)

/-! ## The tools do not fall when their arguments grow -/

/-- `rootUp` does not fall when its argument grows. -/
theorem rootUp_le_rootUp (a b : Int) (h : a ≤ b) : rootUp a ≤ rootUp b := by
  unfold rootUp
  have := isqrt_le_isqrt a.toNat b.toNat (by omega)
  omega

/-- `shiftUp` does not fall when its first argument grows. -/
theorem shiftUp_le_shiftUp (a b : Int) (k : Nat) (h : a ≤ b) : shiftUp a k ≤ shiftUp b k := by
  unfold shiftUp
  exact Int.ediv_le_ediv (Int.pow_pos (by decide)) (by omega)

/-- `roundedLength` does not fall when the length grows. -/
theorem roundedLength_le (count : Nat) (a b : Int) (shift : Nat) (h : a ≤ b) :
    roundedLength count a shift ≤ roundedLength count b shift :=
  shiftUp_le_shiftUp _ _ _ (by omega)

/-- `roundedLength` of a length that is not negative is not negative. -/
theorem roundedLength_nonneg (count : Nat) (a : Int) (shift : Nat) (h : 0 ≤ a) :
    0 ≤ roundedLength count a shift := by
  apply shiftUp_nonneg
  have power : (0 : Int) < 2 ^ (shift - 1) := Int.pow_pos (by decide)
  have := Int.mul_nonneg (Int.le_of_lt power) (rootUp_spec count).1
  omega

/-- A product of two numbers that are not negative does not fall when both grow. -/
theorem mul_le_mul_of_bounds (a b A B : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B) :
    0 ≤ a * b ∧ a * b ≤ A * B :=
  ⟨Int.mul_nonneg ha hb, Int.mul_le_mul hA hB hb (Int.le_trans ha hA)⟩

/-- `ballRadius` is not negative, and it does not fall when the row's length grows. -/
theorem ballRadius_le (width bits shift : Nat) (eps a b : Int) (nonneg : 0 ≤ a)
    (h : a ≤ b) :
    0 ≤ ballRadius width bits shift eps a ∧
      ballRadius width bits shift eps a ≤ ballRadius width bits shift eps b := by
  have square := (mul_le_mul_of_bounds a a b b nonneg nonneg h h).2
  have root := isqrt_le_isqrt (a * a + eps).toNat (b * b + eps).toNat (by omega)
  have power : (0 : Int) < 2 ^ bits := Int.pow_pos (by decide)
  have half : (0 : Int) < 2 ^ (shift - 1) := Int.pow_pos (by decide)
  have rounding := Int.mul_nonneg (Int.le_of_lt half) (rootUp_spec width).1
  have quotient : 0 ≤ (2 : Int) ^ bits / (integerSquareRoot eps.toNat : Int) :=
    Int.ediv_nonneg (Int.le_of_lt power) (by omega)
  unfold ballRadius
  exact ⟨shiftUp_nonneg (by omega) _, shiftUp_le_shiftUp _ _ _ (by omega)⟩

/-! ## Each bound of the check is at most its uniform bound -/

/-- A column's sum of squares is not negative and at most its uniform bound. -/
theorem columnSquares_le (W : Matrix) (rows column : Nat) (entry : Int)
    (within : MatrixWithin entry W) :
    0 ≤ columnSquares W rows column ∧ columnSquares W rows column ≤ rows * (entry * entry) := by
  refine ⟨sumSquaresOver_nonneg _ _, ?_⟩
  unfold columnSquares sumSquaresOver
  rw [← sumOver_const]
  exact sumOver_le_sumOver _ _ _ fun k _ => square_le_square _ _ (within k column)

/-- `columnBoundInBall` is not negative and at most its uniform bound, at a radius that is no
smaller. -/
theorem columnBoundInBall_le (radius larger : Int) (W : Matrix) (rows column : Nat) (entry : Int)
    (within : MatrixWithin entry W) (nonneg : 0 ≤ radius) (le : radius ≤ larger) :
    0 ≤ columnBoundInBall radius W rows column ∧
      columnBoundInBall radius W rows column ≤ uniformColumnBoundInBall larger rows entry := by
  have box := boxColumnBound_le W rows column entry within
  have boxNonneg := boxColumnBound_nonneg W rows column
  have squares := columnSquares_le W rows column entry within
  have radii := mul_le_mul_of_bounds radius radius larger larger nonneg nonneg le le
  have product := mul_le_mul_of_bounds _ _ _ _ radii.1 squares.1 radii.2 squares.2
  have root := isqrt_le_isqrt (radius * radius * columnSquares W rows column).toNat
    (larger * larger * (rows * (entry * entry))).toNat (by omega)
  unfold columnBoundInBall uniformColumnBoundInBall ballColumnBound
  omega

/-- `frobeniusStretch` is not negative and at most its uniform bound. -/
theorem frobeniusStretch_le (W : Matrix) (rows columns : Nat) (entry : Int)
    (within : MatrixWithin entry W) :
    0 ≤ frobeniusStretch W rows columns ∧
      frobeniusStretch W rows columns ≤ uniformFrobenius rows columns entry := by
  refine ⟨(rootUp_spec _).1, rootUp_le_rootUp _ _ ?_⟩
  rw [← sumOver_const]
  exact sumOver_le_sumOver _ _ _ fun column _ => (columnSquares_le W rows column entry within).2

/-- `hiddenLength` is not negative and at most its uniform bound. -/
theorem hiddenLength_le (tables : Tables) (hidden upShift : Nat) (stretch radius silu : Int)
    (largerStretch largerRadius : Int) (siluWithin : largestMagnitude tables.silu.entries ≤ silu)
    (stretchNonneg : 0 ≤ stretch) (stretchLe : stretch ≤ largerStretch)
    (radiusNonneg : 0 ≤ radius) (radiusLe : radius ≤ largerRadius) :
    0 ≤ hiddenLength tables hidden upShift stretch radius ∧
      hiddenLength tables hidden upShift stretch radius ≤
        uniformHiddenLength silu hidden upShift largerStretch largerRadius := by
  have product := mul_le_mul_of_bounds _ _ _ _ stretchNonneg radiusNonneg stretchLe radiusLe
  exact mul_le_mul_of_bounds _ _ _ _ (largestMagnitude_nonneg _)
    (roundedLength_nonneg _ _ _ product.1) siluWithin (roundedLength_le _ _ _ _ product.2)

/-- `attentionAdditionLength` is not negative, and it does not fall when the stretch grows. -/
theorem attentionAdditionLength_le (s : Settings) (p : LayerSettings) (stretch larger : Int)
    (nonneg : 0 ≤ stretch) (le : stretch ≤ larger) :
    0 ≤ attentionAdditionLength s p stretch ∧
      attentionAdditionLength s p stretch ≤ attentionAdditionLength s p larger := by
  have mixed : 0 ≤ mixedLength s := (rootUp_spec _).1
  have product := mul_le_mul_of_bounds _ _ _ _ nonneg mixed le (Int.le_refl _)
  exact ⟨roundedLength_nonneg _ _ _ product.1, roundedLength_le _ _ _ _ product.2⟩

/-- `feedForwardAdditionLength` is not negative and at most its uniform bound. -/
theorem feedForwardAdditionLength_le (s : Settings) (tables : Tables)
    (numbers : StretchNumbers) (bound : UniformStretch) (l : Nat) (hl : l < s.layers)
    (radius larger silu : Int) (siluWithin : largestMagnitude tables.silu.entries ≤ silu)
    (within : StretchNumbersWithin s numbers bound) (nonneg : 0 ≤ radius) (le : radius ≤ larger) :
    0 ≤ feedForwardAdditionLength s tables numbers l radius ∧
      feedForwardAdditionLength s tables numbers l radius ≤
        uniformFeedForwardAdditionLength s silu bound l larger := by
  obtain ⟨_, up, down, routed⟩ := within l hl
  have block : ∀ (hidden upShift : Nat) (stretchUp stretchDown boundUp boundDown : Int),
      0 ≤ stretchUp → stretchUp ≤ boundUp → 0 ≤ stretchDown → stretchDown ≤ boundDown →
      0 ≤ stretchDown * hiddenLength tables hidden upShift stretchUp radius ∧
        stretchDown * hiddenLength tables hidden upShift stretchUp radius ≤
          boundDown * uniformHiddenLength silu hidden upShift boundUp larger := by
    intro hidden upShift stretchUp stretchDown boundUp boundDown up0 up1 down0 down1
    have hiddenBound := hiddenLength_le tables hidden upShift stretchUp radius silu boundUp larger
      siluWithin up0 up1 nonneg le
    exact mul_le_mul_of_bounds _ _ _ _ down0 hiddenBound.1 down1 hiddenBound.2
  unfold feedForwardAdditionLength uniformFeedForwardAdditionLength
  cases s.isMixture l with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    have shared := block s.hidden (s.perLayer.entry l).upShift _ _ _ _ up.1 up.2 down.1 down.2
    exact ⟨roundedLength_nonneg _ _ _ shared.1, roundedLength_le _ _ _ _ shared.2⟩
  | true =>
    simp only [if_true]
    have shared := block s.expertHidden (s.perLayer.entry l).upShift _ _ _ _ up.1 up.2 down.1
      down.2
    have each := fun e => block s.expertHidden (s.perLayer.entry l).routedUpShift _ _ _ _
      (routed e).1.1 (routed e).1.2 (routed e).2.1 (routed e).2.2
    have first := (maxUpTo_spec (fun e => numbers.routedDown l e *
      hiddenLength tables s.expertHidden (s.perLayer.entry l).routedUpShift
        (numbers.routedUp l e) radius) (s.experts - 1)).1 0 (by omega)
    have largest := maxUpTo_le (fun e => numbers.routedDown l e *
      hiddenLength tables s.expertHidden (s.perLayer.entry l).routedUpShift
        (numbers.routedUp l e) radius) (s.experts - 1) _ fun e _ => (each e).2
    have zero := (each 0).1
    simp only at first
    exact ⟨roundedLength_nonneg _ _ _ (by omega), roundedLength_le _ _ _ _ (by omega)⟩

/-- `embeddingLength` is not negative and at most its uniform bound. -/
theorem embeddingLength_le (s : Settings) (weights : Weights) (embedding : Int)
    (within : MatrixWithin embedding weights.embedding) :
    0 ≤ embeddingLength s weights ∧
      embeddingLength s weights ≤ rootUp (s.width * (embedding * embedding)) := by
  refine ⟨(rootUp_spec _).1, rootUp_le_rootUp _ _ (maxUpTo_le _ _ _ fun token _ => ?_)⟩
  unfold sumSquaresOver
  rw [← sumOver_const]
  exact sumOver_le_sumOver _ _ _ fun k _ => square_le_square _ _ (within token k)

/-- `streamLength` is not negative and at most its uniform bound, up to the last layer. -/
theorem streamLength_le (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) (bound : UniformStretch) (silu embedding : Int)
    (siluWithin : largestMagnitude tables.silu.entries ≤ silu)
    (embeddingWithin : MatrixWithin embedding weights.embedding)
    (within : StretchNumbersWithin s numbers bound) (l : Nat) (hl : l ≤ s.layers) :
    0 ≤ streamLength s tables weights numbers l ∧
      streamLength s tables weights numbers l ≤
        uniformStreamLength s silu embedding bound l := by
  induction l with
  | zero => exact embeddingLength_le s weights embedding embeddingWithin
  | succ l ih =>
    have below := ih (by omega)
    have output := (within l (by omega)).1
    have attention := attentionAdditionLength_le s (s.perLayer.entry l) _ _ output.1 output.2
    have radius := ballRadius_le s.width (s.perLayer.entry l).feedForwardBits
      (s.perLayer.entry l).feedForwardShift (s.perLayer.entry l).feedForwardEps
      (streamLength s tables weights numbers l +
        attentionAdditionLength s (s.perLayer.entry l) (numbers.output l))
      (uniformStreamLength s silu embedding bound l +
        attentionAdditionLength s (s.perLayer.entry l) (bound.output l)) (by omega) (by omega)
    have fed := feedForwardAdditionLength_le s tables numbers bound l (by omega) _ _ silu
      siluWithin within radius.1 radius.2
    simp only [streamLength, uniformStreamLength, feedForwardRadius]
    omega

/-- `normFitsLength` passes at a shorter row, if it passes at a longer one. -/
theorem normFitsLength_of_le (bits shift : Nat) (eps a b : Int) (nonneg : 0 ≤ a) (le : a ≤ b)
    (fits : normFitsLength bits shift eps b = true) : normFitsLength bits shift eps a = true := by
  simp only [normFitsLength, Bool.and_eq_true, decide_eq_true_eq] at fits ⊢
  have square := (mul_le_mul_of_bounds a a b b nonneg nonneg le le).2
  have root := isqrt_le_isqrt (a * a + eps).toNat (b * b + eps).toNat (by omega)
  exact ⟨by omega, Int.le_trans (roundShift_le_roundShift _ _ _ (by omega)) fits.2⟩

/-! ## Each test of the check follows from its uniform test -/

/-- `attentionFitsInBall` passes, if the three uniform tests do at a radius that is no smaller. -/
theorem attentionFitsInBall_of_uniform (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (rotary entry radius larger : Int)
    (cosines : MatrixWithin rotary tables.cosine) (sines : MatrixWithin rotary tables.sine)
    (scale : 2 ^ s.rotaryScale ≤ rotary) (within : LayerWithin entry w) (nonneg : 0 ≤ radius)
    (le : radius ≤ larger)
    (query : roundShift (rotary * uniformColumnBoundInBall larger s.width entry +
      rotary * uniformColumnBoundInBall larger s.width entry) p.queryShift ≤ 32767)
    (key : roundShift (rotary * uniformColumnBoundInBall larger s.width entry +
      rotary * uniformColumnBoundInBall larger s.width entry) p.keyShift ≤ 32767)
    (value : roundShift (uniformColumnBoundInBall larger s.width entry) p.valueShift ≤ 32767) :
    attentionFitsInBall s p tables w radius = true := by
  have positive : (0 : Int) < 2 ^ s.rotaryScale := Int.pow_pos (by decide)
  simp only [attentionFitsInBall, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq]
  refine ⟨fun t _ => ⟨fun j _ => ?_, fun j _ => ?_⟩, fun j _ => ?_⟩
  · exact Int.le_trans (roundShift_le_roundShift _ _ _ (rotatedBound_le _ _ _ _ _ rotary _
      (fun i => cosineRow_le s p tables t i rotary cosines scale)
      (fun i => sineRow_le s p tables t i rotary sines (by omega))
      (fun j => (columnBoundInBall_le radius larger _ _ j entry within.1 nonneg le).1)
      (fun j => (columnBoundInBall_le radius larger _ _ j entry within.1 nonneg le).2))) query
  · exact Int.le_trans (roundShift_le_roundShift _ _ _ (rotatedBound_le _ _ _ _ _ rotary _
      (fun i => cosineRow_le s p tables t i rotary cosines scale)
      (fun i => sineRow_le s p tables t i rotary sines (by omega))
      (fun j => (columnBoundInBall_le radius larger _ _ j entry within.2.1 nonneg le).1)
      (fun j => (columnBoundInBall_le radius larger _ _ j entry within.2.1 nonneg le).2))) key
  · exact Int.le_trans (roundShift_le_roundShift _ _ _
      (columnBoundInBall_le radius larger _ _ j entry within.2.2.1 nonneg le).2) value

/-- `unitsFitInBall` passes, if `uniformUnitsFitInBall` does at a radius that is no smaller. -/
theorem unitsFitInBall_of_uniform (w : GatedWeights) (width hidden gateShift upShift : Nat)
    (entry radius larger : Int) (within : GatedWithin entry w) (nonneg : 0 ≤ radius)
    (le : radius ≤ larger)
    (fits : uniformUnitsFitInBall width entry gateShift upShift larger = true) :
    unitsFitInBall w width hidden gateShift upShift radius = true := by
  simp only [uniformUnitsFitInBall, Bool.and_eq_true, decide_eq_true_eq] at fits
  simp only [unitsFitInBall, allBelow_spec, Bool.and_eq_true, decide_eq_true_eq]
  exact fun j _ => ⟨Int.le_trans (roundShift_le_roundShift _ _ _
      (columnBoundInBall_le radius larger _ _ j entry within.1 nonneg le).2) fits.1,
    Int.le_trans (roundShift_le_roundShift _ _ _
      (columnBoundInBall_le radius larger _ _ j entry within.2.1 nonneg le).2) fits.2⟩

/-- `feedForwardFitsInBall` passes, if the uniform tests do at a radius that is no smaller. -/
theorem feedForwardFitsInBall_of_uniform (s : Settings) (p : LayerSettings) (w : LayerWeights)
    (mixture : Bool) (entry radius larger : Int) (within : LayerWithin entry w)
    (nonneg : 0 ≤ radius) (le : radius ≤ larger)
    (shared : uniformUnitsFitInBall s.width entry p.gateShift p.upShift larger = true)
    (routed : mixture = false ∨
      (roundShift (uniformColumnBoundInBall larger s.width entry) p.routerShift ≤ 262143 ∧
        uniformUnitsFitInBall s.width entry p.routedGateShift p.routedUpShift larger = true)) :
    feedForwardFitsInBall s p w mixture radius = true := by
  cases mixture with
  | false =>
    simp only [feedForwardFitsInBall, Bool.false_eq_true, if_false]
    exact unitsFitInBall_of_uniform _ _ _ _ _ entry radius larger within.2.2.2.2.1 nonneg le shared
  | true =>
    rcases routed with impossible | routed
    · exact absurd impossible (by decide)
    · simp only [feedForwardFitsInBall, if_true, Bool.and_eq_true, allBelow_spec,
        decide_eq_true_eq]
      exact ⟨unitsFitInBall_of_uniform _ _ _ _ _ entry radius larger within.2.2.2.2.1 nonneg le
          shared,
        fun e _ => ⟨Int.le_trans (roundShift_le_roundShift _ _ _
          (columnBoundInBall_le radius larger _ _ e entry within.2.2.2.2.2.1 nonneg le).2) routed.1,
          unitsFitInBall_of_uniform _ _ _ _ _ entry radius larger (within.2.2.2.2.2.2 e) nonneg le
            routed.2⟩⟩

/-- **If the four numbers bound what they stand for, the stretch numbers are within `bound`, the
tables pass `routedInputFits`, and `uniformLengthCheck` passes, the length check passes with these
stretch numbers.** -/
theorem lengthWorstCaseCheck_of_uniformLengthCheck (s : Settings) (tables : Tables)
    (weights : Weights) (numbers : StretchNumbers) (rotary silu entry embedding : Int)
    (bound : UniformStretch)
    (cosines : MatrixWithin rotary tables.cosine) (sines : MatrixWithin rotary tables.sine)
    (siluWithin : largestMagnitude tables.silu.entries ≤ silu)
    (routedFit : routedInputFits tables = true)
    (embeddingWithin : MatrixWithin embedding weights.embedding)
    (layersWithin : ∀ l, l < s.layers → LayerWithin entry (weights.perLayer.entry l))
    (numbersWithin : StretchNumbersWithin s numbers bound)
    (passes : uniformLengthCheck s rotary silu entry embedding bound = true) :
    lengthWorstCaseCheck s tables weights numbers = true := by
  simp only [uniformLengthCheck, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq] at passes
  obtain ⟨⟨⟨_, scale⟩, layers⟩, final⟩ := passes
  have stream := streamLength_le s tables weights numbers bound silu embedding siluWithin
    embeddingWithin numbersWithin
  simp only [lengthWorstCaseCheck, Bool.and_eq_true, allBelow_spec]
  refine ⟨⟨routedFit, fun l hl => ?_⟩, ?_⟩
  · have fits := layers l hl
    simp only [uniformLengthLayerFits, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at fits
    obtain ⟨⟨⟨⟨⟨⟨norm1, query⟩, key⟩, value⟩, norm2⟩, shared⟩, routed⟩ := fits
    have within := layersWithin l hl
    have entering := stream l (by omega)
    have output := (numbersWithin l hl).1
    have attention := attentionAdditionLength_le s (s.perLayer.entry l) _ _ output.1 output.2
    have radius1 := ballRadius_le s.width (s.perLayer.entry l).attentionBits
      (s.perLayer.entry l).attentionShift (s.perLayer.entry l).attentionEps _ _ entering.1
      entering.2
    have radius2 := ballRadius_le s.width (s.perLayer.entry l).feedForwardBits
      (s.perLayer.entry l).feedForwardShift (s.perLayer.entry l).feedForwardEps
      (streamLength s tables weights numbers l +
        attentionAdditionLength s (s.perLayer.entry l) (numbers.output l))
      (uniformStreamLength s silu embedding bound l +
        attentionAdditionLength s (s.perLayer.entry l) (bound.output l)) (by omega) (by omega)
    simp only [lengthLayerFits, streamLengthAfterAttention, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact normFitsLength_of_le _ _ _ _ _ entering.1 entering.2 norm1
    · exact attentionFitsInBall_of_uniform s _ tables _ rotary entry _ _ cosines sines scale within
        radius1.1 radius1.2 query key value
    · exact normFitsLength_of_le _ _ _ _ _ (by omega) (by omega) norm2
    · exact feedForwardFitsInBall_of_uniform s _ _ _ entry _ _ within radius2.1 radius2.2 shared
        routed
  · exact normFitsLength_of_le _ _ _ _ _ (stream s.layers (by omega)).1
      (stream s.layers (by omega)).2 final

/-! ## The Frobenius stretch numbers -/

/-- The numbers that bound the Frobenius norms of matrices with every entry within `entry`. -/
def uniformFrobeniusStretch (settings : Settings) (entry : Int) : UniformStretch where
  output _ := uniformFrobenius settings.queryWidth settings.width entry
  up layer := uniformFrobenius settings.width (sharedHidden settings layer) entry
  down layer := uniformFrobenius (sharedHidden settings layer) settings.width entry
  routedUp _ := uniformFrobenius settings.width settings.expertHidden entry
  routedDown _ := uniformFrobenius settings.expertHidden settings.width entry

/-- The Frobenius stretch numbers are within these numbers. -/
theorem frobeniusStretchNumbers_within (s : Settings) (weights : Weights) (entry : Int)
    (layersWithin : ∀ l, l < s.layers → LayerWithin entry (weights.perLayer.entry l)) :
    StretchNumbersWithin s (frobeniusStretchNumbers s weights)
      (uniformFrobeniusStretch s entry) := by
  intro l hl
  have within := layersWithin l hl
  exact ⟨frobeniusStretch_le _ _ _ entry within.2.2.2.1,
    frobeniusStretch_le _ _ _ entry within.2.2.2.2.1.2.1,
    frobeniusStretch_le _ _ _ entry within.2.2.2.2.1.2.2,
    fun e => ⟨frobeniusStretch_le _ _ _ entry (within.2.2.2.2.2.2 e).2.1,
      frobeniusStretch_le _ _ _ entry (within.2.2.2.2.2.2 e).2.2⟩⟩

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.lengthWorstCaseCheck_of_uniformLengthCheck
#print axioms IntegerTransformer.Bounds.frobeniusStretchNumbers_within
