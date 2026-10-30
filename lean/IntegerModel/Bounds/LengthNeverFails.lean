-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/LengthNeverFails.lean

Weights that pass the length check with stretch numbers that hold never fail a range condition.

`allConditionsHold_of_lengthWorstCaseCheck`: for settings, tables and weights that fit together
(`wellFormed`), stretch numbers that hold (`StretchNumbers.Hold`) and with which they pass
`lengthWorstCaseCheck` (IntegerModel/Bounds/LengthCheck.lean), all range conditions hold at all
positions of every prompt (`isPrompt`). Both premises are needed: the test uses the stretch numbers
and does not test them. `frobeniusStretchNumbers_hold`: the Frobenius stretch numbers hold at all
weights. So in `allConditionsHold_of_frobeniusLengthCheck`, beside `wellFormed`, the test is the
only premise on the weights.

The proof, in the order of the file's parts:
1. Lengths and a matrix: the bound on a sum of products with an input in a ball; what a bound on a
   matrix's stretch gives; the Frobenius norm is such a bound.
2. The norm: its result lies in the ball of `ballRadius` (`norm_out_length`), for every row of the
   given length, with no premise on a range condition; conditions 1 and 2 follow from the row's
   length.
3. Conditions 3 to 7 for a vector in the box and the ball.
4. The lengths of what attention and the feed-forward block add to a row of the stream.
5. By induction over the layers, every row of the stream above `l` layers is at most
   `streamLength .. l` long, at every position of every prompt (`stream_length`). The induction
   carries that statement alone. Then each layer's conditions follow from that layer's part of the
   check (`length_layer_conditions`), and the final norm's from the check's last line.

Limits: those at the head of IntegerModel/Bounds/LengthCheck.lean. The theorems say nothing of
weights that do not pass, and this file says of no weights that they pass. Only Lean's core library
is used.
-/
import IntegerModel.Bounds.LengthCheck
import IntegerModel.Bounds.NeverFails

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-- The vector is at most `length` long. -/
def RowLengthWithin (length : Int) (vector : IntegerVector) : Prop :=
  LengthWithin vector.size (fun coordinate => vector.entry coordinate) length

/-! ## 1. Lengths and a matrix -/

/-- The square of the absolute value is the square. -/
theorem magnitude_mul_self (a : Int) : magnitude a * magnitude a = a * a := by
  rw [← magnitude_mul]; unfold magnitude; have := square_nonneg a; omega

/-- A whole number whose square is at most `N` is at most `integerSquareRoot N` in absolute value. -/
theorem magnitude_le_isqrt {c N : Int} (h : c * c ≤ N) : magnitude c ≤ integerSquareRoot N.toNat := by
  have spec := (isqrt_spec N.toNat).2
  have cast : ((integerSquareRoot N.toNat + 1) * (integerSquareRoot N.toNat + 1) : Nat) =
      (((integerSquareRoot N.toNat : Int) + 1) * ((integerSquareRoot N.toNat : Int) + 1) : Int) := by simp
  have lt : (N.toNat : Int) < ((integerSquareRoot N.toNat : Int) + 1) * ((integerSquareRoot N.toNat : Int) + 1) := by
    rw [← cast]; exact Int.ofNat_lt.mpr spec
  have nonneg := square_nonneg c
  have := bounded_of_square_lt c ((integerSquareRoot N.toNat : Int) + 1) (by omega) (by omega)
  rw [magnitude_le_iff]
  omega

/-- The inner product of a vector that is at most `X` long with any vector `g` is at most the root,
rounded down, of `X * X` times the sum of the squares of `g`. -/
theorem magnitude_inner_le_root {n : Nat} {f : Nat → Int} {X : Int} (hf : LengthWithin n f X)
    (g : Nat → Int) :
    magnitude (sumOver n fun k => f k * g k) ≤ integerSquareRoot (X * X * sumSquaresOver n g).toNat := by
  exact magnitude_le_isqrt (Int.le_trans (cauchy_schwarz n f g)
    (Int.mul_le_mul_of_nonneg_right hf.2 (sumSquaresOver_nonneg n g)))

/-- A matrix whose stretch is bounded maps a vector that is at most `X` long to one that is at most
`stretch * X` long. -/
theorem length_of_stretchBound {W : Matrix} {rows columns : Nat} {stretch X : Int} {v : Nat → Int}
    (bound : StretchBound W rows columns stretch) (h : LengthWithin rows v X) :
    LengthWithin columns (fun column => sumOver rows fun row => v row * (W.entry row).entry column)
      (stretch * X) := by
  refine ⟨Int.mul_nonneg bound.1 h.1, ?_⟩
  have first := bound.2 v
  have second := Int.mul_le_mul_of_nonneg_left h.2 (square_nonneg stretch)
  have e : stretch * X * (stretch * X) = stretch * stretch * (X * X) := by grind
  omega

/-- A factor can be taken out of a sum. -/
theorem sumOver_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumOver n (fun k => c * f k) = c * sumOver n f := by
  induction n with
  | zero => simp [sumOver]
  | succ n ih => simp only [sumOver, ih, Int.mul_add]

/-- The Frobenius norm, rounded up, bounds the stretch of a matrix: the Cauchy-Schwarz inequality,
column by column. -/
theorem stretchBound_frobenius (W : Matrix) (rows columns : Nat) :
    StretchBound W rows columns (frobeniusStretch W rows columns) := by
  have root := rootUp_spec (sumOver columns fun column => columnSquares W rows column)
  refine ⟨root.1, fun v => ?_⟩
  unfold frobeniusStretch
  have each : sumSquaresOver columns
      (fun column => sumOver rows fun row => v row * (W.entry row).entry column)
      ≤ sumOver columns fun column => sumSquaresOver rows v * columnSquares W rows column :=
    sumOver_le_sumOver _ _ _ fun column _ =>
      cauchy_schwarz rows v fun row => (W.entry row).entry column
  rw [sumOver_mul_left] at each
  have scaled := Int.mul_le_mul_of_nonneg_left root.2 (sumSquaresOver_nonneg rows v)
  rw [Int.mul_comm (sumSquaresOver rows v) (_ * _)] at scaled
  exact Int.le_trans each scaled

/-! ## 2. The norm -/

/-- The clamp makes no square larger. -/
theorem clamp_square_le (a b : Int) (h : 0 ≤ b) : clamp a b * clamp a b ≤ a * a := by
  have small : magnitude (clamp a b) ≤ magnitude a := by
    unfold clamp magnitude; omega
  have := square_le_square _ _ small
  rw [magnitude_mul_self] at this
  exact this

/-- **The ball.** The result of a norm that reads a row at most `X` long is at most
`ballRadius .. X` long. No range condition is a premise: the largest root comes from the row's own
length. -/
theorem norm_out_length (bits shift : Nat) (eps : Int) (x : IntegerVector) (X : Int) (eps_pos : 1 ≤ eps)
    (shift_pos : 1 ≤ shift) (h : RowLengthWithin X x) :
    RowLengthWithin (ballRadius x.size bits shift eps X) (rmsNorm bits shift eps x).out := by
  unfold RowLengthWithin at *
  rw [(size_rmsNorm bits shift eps x).2]
  unfold ballRadius
  have rootPos := root_positive bits shift eps x eps_pos
  have reciprocal : (rmsNorm bits shift eps x).reciprocal =
      (2 ^ bits + (rmsNorm bits shift eps x).root / 2) / (rmsNorm bits shift eps x).root := rfl
  have root : (rmsNorm bits shift eps x).root =
      integerSquareRoot ((rmsNorm bits shift eps x).sumSquares + eps).toNat := rfl
  have sum : (rmsNorm bits shift eps x).sumSquares = sumSquaresOver x.size fun k => x.entry k := rfl
  have sumNonneg : 0 ≤ (rmsNorm bits shift eps x).sumSquares := by
    rw [sum]; exact sumSquaresOver_nonneg _ _
  have outAt : ∀ k, k < x.size → (rmsNorm bits shift eps x).out.entry k =
      clamp (roundShift (x.entry k * (rmsNorm bits shift eps x).reciprocal) shift)
        activationBound := by
    intro k hk
    simp only [rmsNorm, map_read, Array.size_map, hk]
  have spec := (isqrt_spec ((rmsNorm bits shift eps x).sumSquares + eps).toNat).2
  have rootLow : (integerSquareRoot eps.toNat : Int) ≤ (rmsNorm bits shift eps x).root := by
    rw [root]; exact Int.ofNat_le.mpr (isqrt_le_isqrt _ _ (by omega))
  have rootHigh : (rmsNorm bits shift eps x).root ≤ (integerSquareRoot (X * X + eps).toNat : Int) := by
    rw [root]
    have := h.2
    rw [← sum] at this
    exact Int.ofNat_le.mpr (isqrt_le_isqrt _ _ (by omega))
  have leastPos : (1 : Int) ≤ (integerSquareRoot eps.toNat : Int) := by
    have one := (isqrt_spec eps.toNat).2
    have : integerSquareRoot eps.toNat ≠ 0 := by
      intro zero
      rw [zero] at one
      omega
    omega
  have castHigh : ((integerSquareRoot ((rmsNorm bits shift eps x).sumSquares + eps).toNat + 1) *
      (integerSquareRoot ((rmsNorm bits shift eps x).sumSquares + eps).toNat + 1) : Nat) =
      (((rmsNorm bits shift eps x).root + 1) * ((rmsNorm bits shift eps x).root + 1) : Int) := by
    rw [root]; simp
  have row : LengthWithin x.size (fun k => x.entry k) ((rmsNorm bits shift eps x).root + 1) := by
    refine ⟨by omega, ?_⟩
    rw [← sum]
    have : (((rmsNorm bits shift eps x).sumSquares + eps).toNat : Int) <
        ((rmsNorm bits shift eps x).root + 1) * ((rmsNorm bits shift eps x).root + 1) := by
      rw [← castHigh]; exact Int.ofNat_lt.mpr spec
    omega
  generalize (rmsNorm bits shift eps x).reciprocal = R at *
  generalize (rmsNorm bits shift eps x).root = σ at *
  generalize (integerSquareRoot eps.toNat : Int) = least at *
  generalize (integerSquareRoot (X * X + eps).toNat : Int) = most at *
  have power : (0 : Int) < 2 ^ bits := Int.pow_pos (by decide)
  have product : R * σ ≤ 2 ^ bits + σ / 2 := by rw [reciprocal]; exact Int.ediv_mul_le _ (by omega)
  have Rnonneg : 0 ≤ R := by rw [reciprocal]; exact Int.ediv_nonneg (by omega) (by omega)
  have Rsmall : R ≤ 2 ^ bits / least + 1 := by
    have quotientNonneg : 0 ≤ (2 : Int) ^ bits / least := Int.ediv_nonneg (by omega) (by omega)
    by_cases zero : R = 0
    · omega
    · have step : (R - 1) * least ≤ (R - 1) * σ :=
        Int.mul_le_mul_of_nonneg_left rootLow (by omega)
      have expand : (R - 1) * σ = R * σ - σ := by grind
      have : R - 1 ≤ 2 ^ bits / least := (Int.le_ediv_iff_mul_le (by omega)).mpr (by omega)
      omega
  have scaled := length_scale row Rnonneg
  have expand : R * (σ + 1) = R * σ + R := by grind
  have raised := length_of_le scaled
    (show R * (σ + 1) ≤ 2 ^ bits + most / 2 + 2 ^ bits / least + 1 by omega)
  have rounded := length_roundShift raised shift shift_pos
  unfold roundedLength at rounded
  refine length_of_entries rounded fun k hk => ?_
  rw [outAt k hk, Int.mul_comm (x.entry k) R]
  exact clamp_square_le _ _ (by decide)

/-- Conditions 1 and 2 at one norm, from a bound on the length of the row that it reads. -/
theorem normOk_of_normFitsLength (bits shift : Nat) (eps : Int) (x : IntegerVector) (X : Int)
    (eps_pos : 1 ≤ eps) (h : RowLengthWithin X x) (fits : normFitsLength bits shift eps X = true) :
    normOk eps (rmsNorm bits shift eps x) = true := by
  simp only [normFitsLength, Bool.and_eq_true, decide_eq_true_eq] at fits
  have sum : (rmsNorm bits shift eps x).sumSquares ≤ X * X := h.2
  simp only [normOk, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, ?_⟩
  apply fits16_of_bounded _ _ _ fits.2
  intro k inside
  rw [(size_rmsNorm bits shift eps x).1] at inside
  apply Int.le_trans (norm_quotient_le bits shift eps x k inside eps_pos)
  apply roundShift_le_roundShift
  have root : (rmsNorm bits shift eps x).root =
      integerSquareRoot ((rmsNorm bits shift eps x).sumSquares + eps).toNat := rfl
  have mono := isqrt_le_isqrt ((rmsNorm bits shift eps x).sumSquares + eps).toNat
    (X * X + eps).toNat (by omega)
  rw [root]
  omega

/-! ## 3. Conditions 3 to 7 for a vector in the box and the ball -/

/-- Every read of a product with an input in the box and the ball, inside or outside. -/
theorem product_read_le_columnBoundInBall (a : IntegerVector) (W : Matrix) (outputs width : Nat)
    (radius : Int) (size : a.size = width) (box : InBox a) (ball : RowLengthWithin radius a)
    (j : Nat) :
    magnitude ((product a W outputs).entry j) ≤ columnBoundInBall radius W width j := by
  unfold columnBoundInBall
  have fromBox := product_read_le a W outputs width size box j
  have fromBall : magnitude ((product a W outputs).entry j) ≤ ballColumnBound radius W width j := by
    unfold ballColumnBound columnSquares
    by_cases inside : j < outputs
    · unfold product
      rw [tabulate_read _ _ _ inside, ← size]
      exact magnitude_inner_le_root ball _
    · rw [entry_outside _ j (by rw [size_product]; exact inside)]
      show magnitude 0 ≤ _
      unfold magnitude
      omega
  omega

/-- A rotated and shifted vector fits 16 bits, if its bounds do. -/
theorem rotated_fits_of (cosine sine : IntegerVector) (headDim : Nat) (A : IntegerVector) (shift : Nat)
    (productBound : Nat → Int) (h : ∀ j, magnitude (A.entry j) ≤ productBound j)
    (fits : ∀ j, j < A.size →
      roundShift (rotatedBound cosine sine headDim productBound j) shift ≤ 32767) :
    fits16 ((rotate cosine sine headDim A).map fun e => roundShift e shift) = true := by
  apply fits16_of_bounded _ 32767 _ (Int.le_refl _)
  intro j inside
  rw [Array.size_map, size_rotate] at inside
  rw [map_read _ _ _ (by rw [size_rotate]; exact inside)]
  apply Int.le_trans _ (fits j inside)
  apply magnitude_roundShift_le
  exact magnitude_rotate_entry_le cosine sine headDim _ _ h j inside

/-- A product with an input in the box and the ball, shifted. -/
theorem shifted_read_le_columnBoundInBall (z : IntegerVector) (W : Matrix) (outputs shift width j : Nat)
    (radius : Int) (size : z.size = width) (box : InBox z) (ball : RowLengthWithin radius z)
    (inside : j < outputs) :
    magnitude (((product z W outputs).map fun e => roundShift e shift).entry j) ≤
      roundShift (columnBoundInBall radius W width j) shift := by
  rw [map_read _ _ _ (by rw [size_product]; exact inside)]
  exact magnitude_roundShift_le _ _ _
    (product_read_le_columnBoundInBall z W outputs width radius size box ball j)

/-- Conditions 3 and 4 at one position, for any vector in the box and the ball. -/
theorem projections_fit_inBall (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights)
    (t : Nat) (a : IntegerVector) (radius : Int) (position : t < s.positions) (size : a.size = s.width)
    (box : InBox a) (ball : RowLengthWithin radius a)
    (fits : attentionFitsInBall s p tables w radius = true) :
    fits16 (projections s p tables w t a).wideQuery = true ∧
    fits16 (projections s p tables w t a).wideKey = true ∧
    fits16 (projections s p tables w t a).wideValue = true := by
  simp only [attentionFitsInBall, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq] at fits
  have products := fun (W : Matrix) (outputs : Nat) =>
    product_read_le_columnBoundInBall a W outputs s.width radius size box ball
  refine ⟨?_, ?_, ?_⟩
  · exact rotated_fits_of (cosineRow s p tables t) (sineRow s p tables t) s.headDim _ p.queryShift _
      (products w.query s.queryWidth) (by rw [size_product]; exact (fits.1 t position).1)
  · exact rotated_fits_of (cosineRow s p tables t) (sineRow s p tables t) s.headDim _ p.keyShift _
      (products w.key s.keyValueWidth) (by rw [size_product]; exact (fits.1 t position).2)
  · apply fits16_of_bounded _ 32767 _ (Int.le_refl _)
    intro j inside
    rw [(size_projections s p tables w t a).2.2.1] at inside
    exact Int.le_trans
      (shifted_read_le_columnBoundInBall a w.value s.keyValueWidth p.valueShift s.width j radius
        size box ball inside)
      (fits.2 j inside)

/-- Conditions 6 and 7 of one gated block, for any vector in the box and the ball. -/
theorem hiddenUnits_fit_inBall (tables : Tables) (w : GatedWeights)
    (width hidden gateShift upShift : Nat) (z : IntegerVector) (radius : Int) (size : z.size = width)
    (box : InBox z) (ball : RowLengthWithin radius z)
    (fits : unitsFitInBall w width hidden gateShift upShift radius = true) :
    unitsOk (hiddenUnits tables w hidden gateShift upShift z) = true := by
  rw [unitsFitInBall, allBelow_spec] at fits
  have sizes := size_hiddenUnits tables w hidden gateShift upShift z
  simp only [unitsOk, Bool.and_eq_true]
  constructor
  · apply all_of_entries
    intro j inside
    rw [sizes.2.2.1] at inside
    have fit := fits j inside
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
    have gate :=
      shifted_read_le_columnBoundInBall z w.gate hidden gateShift width j radius size
        box ball inside
    have made : (hiddenUnits tables w hidden gateShift upShift z).highPart.entry j =
        ((((product z w.gate hidden).map fun e => roundShift e gateShift).entry j) -
          balancedLowByte (((product z w.gate hidden).map fun e => roundShift e gateShift).entry j))
            / 256 := by
      simp only [hiddenUnits, tabulate_read, map_read, size_product, Array.size_map, inside]
    rw [made]
    generalize ((product z w.gate hidden).map fun e => roundShift e gateShift).entry j = g at gate
    rw [magnitude_le_iff] at gate
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    unfold balancedLowByte
    omega
  · apply fits16_of_bounded _ 32767 _ (Int.le_refl _)
    intro j inside
    rw [sizes.2.2.2.2.2.2] at inside
    have fit := fits j inside
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
    exact Int.le_trans
      (shifted_read_le_columnBoundInBall z w.up hidden upShift width j radius size box ball inside)
      fit.2

/-- The routed expert's input is, entry by entry, no larger than the normed row. -/
theorem magnitude_scaled_le (largest scale m : Int)
    (fits : roundShift (largest * activationBound) 16 ≤ activationBound)
    (small : magnitude scale ≤ largest) (box : magnitude m ≤ activationBound) :
    magnitude (roundShift (scale * m) 16) ≤ magnitude m := by
  unfold activationBound at *
  have cap : largest ≤ 65552 := by
    unfold roundShift at fits
    omega
  have first : magnitude (scale * m) ≤ 65552 * magnitude m :=
    Int.le_trans (magnitude_mul_le scale m largest small)
      (Int.mul_le_mul_of_nonneg_right cap (magnitude_nonneg m))
  apply Int.le_trans (magnitude_roundShift_le _ _ 16 first)
  have nonneg := magnitude_nonneg m
  unfold roundShift
  generalize magnitude m = a at *
  omega

/-- The routed expert's input lies in the same ball as the normed row. -/
theorem routedExpert_input_inBall (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (m : IntegerVector) (radius : Int) (box : InBox m) (ball : RowLengthWithin radius m)
    (fits : routedInputFits tables = true) :
    RowLengthWithin radius (routedExpert s p tables w m).input := by
  have made : (routedExpert s p tables w m).input =
      m.map fun mk => roundShift ((routedExpert s p tables w m).scale * mk) 16 := rfl
  simp only [routedInputFits, decide_eq_true_eq] at fits
  unfold RowLengthWithin at *
  rw [made, Array.size_map]
  refine length_of_entries ball fun k inside => ?_
  rw [map_read _ _ _ inside]
  have small := magnitude_scaled_le _ _ (m.entry k) fits
    (magnitude_read_le tables.sigmoid _ : magnitude (routedExpert s p tables w m).scale ≤ _) (box k)
  have := square_le_square _ _ small
  rw [magnitude_mul_self] at this
  exact this

/-- Condition 5, for any vector in the box and the ball. -/
theorem routedExpert_high_fits_inBall (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (m : IntegerVector) (radius : Int) (size : m.size = s.width) (box : InBox m)
    (ball : RowLengthWithin radius m)
    (fits : ∀ e, e < s.experts →
      roundShift (columnBoundInBall radius w.router s.width e) p.routerShift ≤ 262143) :
    fits16 (routedExpert s p tables w m).high = true := by
  have sizes := size_routedExpert s p tables w m
  unfold fits16
  apply all_of_entries
  intro e inside
  rw [sizes.2.1] at inside
  have wide := shifted_read_le_columnBoundInBall m w.router s.experts p.routerShift s.width e radius
    size box ball inside
  have made : (routedExpert s p tables w m).high.entry e =
      (((product m w.router s.experts).map fun e => roundShift e p.routerShift).entry e) / 8 := by
    simp only [routedExpert, map_read, size_product, Array.size_map, inside]
  rw [made]
  have fit := fits e inside
  generalize ((product m w.router s.experts).map fun e => roundShift e p.routerShift).entry e = lw
    at wide
  rw [magnitude_le_iff] at wide
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-! ## 4. The lengths of the additions -/

/-- The triangle inequality for `addVectors`. -/
theorem addVec_length (x y : IntegerVector) (X Y : Int) (size : y.size = x.size) (hx : RowLengthWithin X x)
    (hy : RowLengthWithin Y y) : RowLengthWithin (X + Y) (addVectors x y) := by
  unfold RowLengthWithin at *
  rw [size_addVec]
  rw [size] at hy
  have sum := length_add hx hy
  refine length_of_entries sum fun k inside => ?_
  unfold addVectors
  rw [tabulate_read _ _ _ inside]
  exact Int.le_refl _

/-- What attention adds to a row of the stream is at most `attentionAdditionLength` long, whatever
the stream is. -/
theorem attention_addition_length (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix) (stretch : Int)
    (some_entry : 0 < tables.exponential.size) (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true) (shift_pos : 1 ≤ p.outputShift)
    (bound : StretchBound w.output s.queryWidth s.width stretch) (t : Nat) (ht : t < x.size) :
    RowLengthWithin (attentionAdditionLength s p stretch)
      ((attention s p tables w x).addition.entry t) := by
  have box := attention_mixed_inBox s p tables w x some_entry first none_negative t ht
  have size := (size_attention_rows s p tables w x t ht).2.1
  have made : (attention s p tables w x).addition.entry t =
      (product ((attention s p tables w x).mixed.entry t) w.output s.width).map
        fun e => roundShift e p.outputShift := by
    simp only [attention, map_read, size_tabulate, ht]
  have mixed : LengthWithin s.queryWidth
      (fun k => ((attention s p tables w x).mixed.entry t).entry k) (mixedLength s) :=
    length_of_bounds (b := fun _ => activationBound) fun k _ => box k
  have rounded := length_roundShift (length_of_stretchBound bound mixed) p.outputShift shift_pos
  unfold RowLengthWithin attentionAdditionLength
  rw [made, Array.size_map, size_product]
  refine length_of_entries rounded fun k inside => ?_
  rw [map_read _ _ _ (by rw [size_product]; exact inside)]
  unfold product
  rw [tabulate_read _ _ _ inside, size]
  exact Int.le_refl _

/-- The products `s[j] u[j]` of one block that reads a vector in the ball. -/
theorem hidden_products_length (tables : Tables) (w : GatedWeights)
    (width hidden gateShift upShift : Nat) (z : IntegerVector) (radius stretchUp : Int)
      (size : z.size = width)
    (shift_pos : 1 ≤ upShift) (ball : RowLengthWithin radius z)
    (bound : StretchBound w.up width hidden stretchUp) :
    LengthWithin hidden
      (fun j => (hiddenUnits tables w hidden gateShift upShift z).activation.entry j
        * (hiddenUnits tables w hidden gateShift upShift z).up.entry j)
      (hiddenLength tables hidden upShift stretchUp radius) := by
  have sizes := size_hiddenUnits tables w hidden gateShift upShift z
  unfold RowLengthWithin at ball
  rw [size] at ball
  have rounded := length_roundShift (length_of_stretchBound bound ball) upShift shift_pos
  have largest : 0 ≤ largestMagnitude tables.silu.entries :=
    Int.le_trans (magnitude_nonneg _) (magnitude_entry_le_largestMagnitude tables.silu.entries 0)
  have scaled := length_scale rounded largest
  unfold hiddenLength
  refine length_of_entries scaled fun j inside => ?_
  have up : (hiddenUnits tables w hidden gateShift upShift z).up.entry j =
      roundShift (sumOver width fun row => z.entry row * (w.up.entry row).entry j) upShift := by
    simp only [hiddenUnits, product, map_read, tabulate_read, size_tabulate, inside, size]
  have activation : magnitude ((hiddenUnits tables w hidden gateShift upShift z).activation.entry j)
    ≤ largestMagnitude tables.silu.entries := by
    have made : (hiddenUnits tables w hidden gateShift upShift z).activation =
        (hiddenUnits tables w hidden gateShift upShift z).key.map tables.silu.read := rfl
    rw [made, map_read _ _ _ (by rw [sizes.2.2.2.2.1]; exact inside)]
    exact magnitude_read_le _ _
  rw [up]
  generalize
    roundShift (sumOver width fun row => z.entry row * (w.up.entry row).entry j) upShift = u
  generalize (hiddenUnits tables w hidden gateShift upShift z).activation.entry j = a at activation
  generalize largestMagnitude tables.silu.entries = S at *
  have square := Int.mul_le_mul_of_nonneg_right (square_le_square a S activation) (square_nonneg u)
  have e1 : a * u * (a * u) = a * a * (u * u) := by grind
  have e2 : S * u * (S * u) = S * S * (u * u) := by grind
  omega

/-- The down projection of one block that reads a vector in the ball, before the shift. -/
theorem downSum_length (tables : Tables) (w : GatedWeights)
    (width hidden gateShift upShift : Nat) (z : IntegerVector) (radius stretchUp stretchDown : Int)
    (size : z.size = width) (shift_pos : 1 ≤ upShift) (ball : RowLengthWithin radius z)
    (boundUp : StretchBound w.up width hidden stretchUp)
    (boundDown : StretchBound w.down hidden width stretchDown) :
    LengthWithin width (fun k => downSum (hiddenUnits tables w hidden gateShift upShift z) w.down k)
      (stretchDown * hiddenLength tables hidden upShift stretchUp radius) := by
  have sizes := size_hiddenUnits tables w hidden gateShift upShift z
  have products := hidden_products_length tables w width hidden gateShift upShift z radius stretchUp
    size shift_pos ball boundUp
  have stretched := length_of_stretchBound boundDown products
  refine length_of_entries stretched fun k _ => ?_
  unfold downSum
  rw [sizes.2.2.2.2.2.2]
  exact Int.le_refl _

/-- What the feed-forward block of layer `l` adds to a row that is at most `X` long. -/
theorem feedForward_addition_length (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) (l : Nat) (hl : l < s.layers)
    (formedLayer :
      layerWellFormed s (s.perLayer.entry l) (weights.perLayer.entry l) (s.isMixture l) = true)
    (holds : numbers.Hold s weights) (routedFit : routedInputFits tables = true)
    (x : IntegerVector) (X : Int) (size : x.size = s.width) (h : RowLengthWithin X x) :
    RowLengthWithin (feedForwardAdditionLength s tables numbers l (feedForwardRadius s l X))
      (feedForward s (s.perLayer.entry l) tables (weights.perLayer.entry l) (s.isMixture l)
        x).addition := by
  have hold := holds l hl
  unfold RowLengthWithin feedForwardAdditionLength feedForwardRadius
  rw [(size_feedForward _ _ _ _ _ _).1]
  unfold sharedHidden at hold
  simp only [layerWellFormed, Bool.and_eq_true, decide_eq_true_eq] at formedLayer
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, eps_pos⟩, _⟩, _⟩, _⟩, _⟩, _⟩, normShift⟩, _⟩, upShift⟩,
    downShift⟩, rest⟩ := formedLayer
  dsimp only
  generalize s.perLayer.entry l = p at *
  generalize weights.perLayer.entry l = w at *
  have box := norm_out_inBox p.feedForwardBits p.feedForwardShift p.feedForwardEps x
  have normed : (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out.size =
      s.width := by rw [(size_rmsNorm _ _ _ _).2, size]
  have ball :=
    norm_out_length p.feedForwardBits p.feedForwardShift p.feedForwardEps x X eps_pos normShift h
  rw [size] at ball
  generalize
    ballRadius s.width p.feedForwardBits p.feedForwardShift p.feedForwardEps X = radius at *
  by_cases mixture : s.isMixture l = true
  · simp only [mixture, if_true, Bool.and_eq_true, decide_eq_true_eq] at rest hold ⊢
    have some_expert := isMixture_experts s l mixture
    have chosen := chosen_index s p tables w
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out some_expert
    have inputBall := routedExpert_input_inBall s p tables w _ radius box ball routedFit
    have inputSize : (routedExpert s p tables w
        (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).input.size =
        s.width := by rw [(size_routedExpert _ _ _ _ _).2.2.2.2, normed]
    have shared := downSum_length tables w.shared s.width s.expertHidden p.gateShift p.upShift _
      radius _ _ normed upShift ball hold.2.1 hold.2.2.1
    have routed := downSum_length tables (w.routed.entry _) s.width s.expertHidden p.routedGateShift
      p.routedUpShift _ radius _ _ inputSize rest.2 inputBall (hold.2.2.2 (by trivial) _ chosen).1
      (hold.2.2.2 (by trivial) _ chosen).2
    have largest := length_of_le routed ((maxUpTo_spec (fun e => numbers.routedDown l e
      * hiddenLength tables s.expertHidden p.routedUpShift (numbers.routedUp l e) radius)
      (s.experts - 1)).1 _ (by omega))
    have rounded := length_roundShift (length_add shared largest) p.downShift downShift
    refine length_of_entries rounded fun k inside => ?_
    simp only [feedForward, if_true, tabulate_read, inside]
    exact Int.le_refl _
  · have dense : s.isMixture l = false := by simpa using mixture
    simp only [dense, Bool.false_eq_true, if_false] at rest hold ⊢
    have shared := downSum_length tables w.shared s.width s.hidden p.gateShift p.upShift _
      radius _ _ normed upShift ball hold.2.1 hold.2.2.1
    have rounded := length_roundShift shared p.downShift downShift
    refine length_of_entries rounded fun k inside => ?_
    simp only [feedForward, Bool.false_eq_true, if_false, tabulate_read, inside]
    exact Int.le_refl _

/-! ## 5. Layers, the induction over the layers, the theorems -/

/-- Every token's embedding is at most `embeddingLength` long. -/
theorem embedding_length (s : Settings) (weights : Weights) (token : Nat)
    (inside : token < s.vocabulary) (size : (weights.embedding.entry token).size = s.width) :
    RowLengthWithin (embeddingLength s weights) (weights.embedding.entry token) := by
  unfold RowLengthWithin embeddingLength
  rw [size]
  refine ⟨(rootUp_spec _).1, Int.le_trans ?_ (rootUp_spec _).2⟩
  exact (maxUpTo_spec (fun token => sumSquaresOver s.width fun k =>
    (weights.embedding.entry token).entry k) (s.vocabulary - 1)).1 token (by omega)

/-- The shifts of a well-formed layer that the lengths need are at least 1. -/
theorem layerWellFormed_shifts (s : Settings) (p : LayerSettings) (w : LayerWeights)
    (mixture : Bool) (h : layerWellFormed s p w mixture = true) :
    1 ≤ p.attentionShift ∧ 1 ≤ p.outputShift ∧ 1 ≤ p.feedForwardShift ∧ 1 ≤ p.upShift ∧
    1 ≤ p.downShift ∧ (mixture = true → 1 ≤ p.routedUpShift) := by
  simp only [layerWellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, a⟩, _⟩, _⟩, _⟩, o⟩, f⟩, _⟩, u⟩, d⟩, rest⟩ := h
  refine ⟨a, o, f, u, d, fun mix => ?_⟩
  simp only [mix, if_true, Bool.and_eq_true, decide_eq_true_eq] at rest
  exact rest.2

/-- The stream after attention, in length. -/
theorem attention_out_length (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) (l : Nat) (hl : l < s.layers) (X : Matrix)
    (formed : wellFormed s tables weights = true) (holds : numbers.Hold s weights)
    (rows : ∀ t, t < X.size → (X.entry t).size = s.width)
    (lengths : ∀ t, t < X.size →
      RowLengthWithin (streamLength s tables weights numbers l) (X.entry t))
    (t : Nat) (ht : t < X.size) :
    RowLengthWithin (streamLengthAfterAttention s tables weights numbers l)
      ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry t) := by
  have parts := wellFormed_spec s tables weights formed
  have shifts := layerWellFormed_shifts _ _ _ _ (parts.2.2.2.2.2.2 l hl)
  have made : (attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry t =
      addVectors (X.entry t)
        ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).addition.entry
          t) := by
    simp only [attention, tabulate_read, ht]
  rw [made]
  apply addVec_length _ _ _ _ _ (lengths t ht)
  · exact attention_addition_length s _ tables _ X _ parts.2.2.1.2.2.1 parts.2.2.1.2.2.2.1
      parts.2.2.1.2.2.2.2.1 shifts.2.1 (holds l hl).1 t ht
  · rw [(size_attention_rows _ _ _ _ _ t ht).2.2.1, rows t ht]

/-- One layer's step on the stream's length. -/
theorem layer_out_length (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) (l : Nat) (hl : l < s.layers) (X : Matrix)
    (formed : wellFormed s tables weights = true) (holds : numbers.Hold s weights)
    (routedFit : routedInputFits tables = true)
    (rows : ∀ t, t < X.size → (X.entry t).size = s.width)
    (lengths : ∀ t, t < X.size →
      RowLengthWithin (streamLength s tables weights numbers l) (X.entry t))
    (t : Nat) (ht : t < X.size) :
    RowLengthWithin (streamLength s tables weights numbers (l + 1))
      ((layer s tables weights l X).out.entry t) := by
  have parts := wellFormed_spec s tables weights formed
  have attended :=
    attention_out_length s tables weights numbers l hl X formed holds rows lengths t ht
  have size : ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry
      t).size = s.width := by
    rw [(size_attention_rows _ _ _ _ _ t ht).2.2.2]; exact rows t ht
  rw [layer_out_read s tables weights l X t ht, feedForward_out]
  apply addVec_length _ _ _ _ _ attended
  · exact feedForward_addition_length s tables weights numbers l hl (parts.2.2.2.2.2.2 l hl)
      holds routedFit _ _ size attended
  · rw [(size_feedForward _ _ _ _ _ _).1, size]

/-- **The induction.** Every row of the stream above `l` layers is at most `streamLength .. l` long,
at every position of every prompt. No range condition is among the premises, and of the check only
`routedInputFits`. -/
theorem stream_length (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) (formed : wellFormed s tables weights = true)
    (holds : numbers.Hold s weights) (routedFit : routedInputFits tables = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) (l : Nat) (hl : l ≤ s.layers)
    (t : Nat) (ht : t < prompt.size) :
    RowLengthWithin (streamLength s tables weights numbers l)
      ((streamAbove (prompt.map fun token => weights.embedding.entry token)
        (firstLayers s tables weights (prompt.map fun token => weights.embedding.entry token)
          l)).entry t) := by
  have parts := wellFormed_spec s tables weights formed
  have shape := embedded_shape s tables weights prompt formed prompt_ok
  induction l generalizing t with
  | zero =>
    rw [streamAbove_zero, map_read _ _ _ ht]
    have token := (isPrompt_spec s prompt prompt_ok).2.2 t ht
    exact embedding_length s weights _ token ((hasSize_spec _ _ _ parts.2.2.2.1.1).2 _ token)
  | succ l ih =>
    rw [streamAbove_succ]
    have stream := stream_shape s tables weights
      (prompt.map fun token => weights.embedding.entry token) s.width l
      (fun t ht => shape.2 t (by rw [← shape.1]; exact ht))
    apply layer_out_length s tables weights numbers l (by omega) _ formed holds routedFit
    · intro t ht
      exact stream.2 t (by rw [← stream.1]; exact ht)
    · intro t ht
      exact ih (by omega) t (by rw [← shape.1, ← stream.1]; exact ht)
    · rw [stream.1, shape.1]; exact ht

/-- Conditions 1 to 4 at one position of one layer. -/
theorem attentionOk_of_fitsInBall (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix) (rowLength : Int) (eps_pos : 1 ≤ p.attentionEps)
    (shift_pos : 1 ≤ p.attentionShift)
    (few : x.size ≤ s.positions) (rows : ∀ t, t < x.size → (x.entry t).size = s.width)
    (lengths : ∀ t, t < x.size → RowLengthWithin rowLength (x.entry t))
    (normFit : normFitsLength p.attentionBits p.attentionShift p.attentionEps rowLength = true)
    (fits : attentionFitsInBall s p tables w
      (ballRadius s.width p.attentionBits p.attentionShift p.attentionEps rowLength) = true)
    (t : Nat) (ht : t < x.size) :
    attentionOk p (attention s p tables w x) t = true := by
  have norm : (attention s p tables w x).norm.entry t =
      rmsNorm p.attentionBits p.attentionShift p.attentionEps (x.entry t) := by
    simp only [attention, map_read, ht]
  have read : (attention s p tables w x).projected.entry t =
      projections s p tables w t ((attention s p tables w x).norm.entry t).out := by
    simp only [attention, tabulate_read, ht]
  have ball := norm_out_length p.attentionBits p.attentionShift p.attentionEps (x.entry t) rowLength
    eps_pos shift_pos (lengths t ht)
  rw [rows t ht] at ball
  have parts := projections_fit_inBall s p tables w t
    (rmsNorm p.attentionBits p.attentionShift p.attentionEps (x.entry t)).out _ (by omega)
    (by rw [(size_rmsNorm _ _ _ _).2, rows t ht]) (norm_out_inBox _ _ _ _) ball fits
  simp only [attentionOk, Bool.and_eq_true]
  rw [read, norm]
  exact ⟨⟨⟨normOk_of_normFitsLength _ _ _ _ rowLength eps_pos (lengths t ht) normFit,
    parts.1⟩, parts.2.1⟩, parts.2.2⟩

/-- Conditions 1, 2, 5, 6 and 7 of one layer's feed-forward block at one position. -/
theorem feedForwardOk_of_fitsInBall (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (mixture : Bool) (x : IntegerVector) (rowLength : Int)
    (some_expert : mixture = true → 0 < s.experts) (eps_pos : 1 ≤ p.feedForwardEps)
    (shift_pos : 1 ≤ p.feedForwardShift)
    (size : x.size = s.width) (length : RowLengthWithin rowLength x)
    (routedFit : routedInputFits tables = true)
    (normFit :
      normFitsLength p.feedForwardBits p.feedForwardShift p.feedForwardEps rowLength = true)
    (fits : feedForwardFitsInBall s p w mixture
      (ballRadius s.width p.feedForwardBits p.feedForwardShift p.feedForwardEps rowLength) = true) :
    feedForwardOk p (feedForward s p tables w mixture x) = true := by
  have box := norm_out_inBox p.feedForwardBits p.feedForwardShift p.feedForwardEps x
  have ball := norm_out_length p.feedForwardBits p.feedForwardShift p.feedForwardEps x rowLength
    eps_pos shift_pos length
  rw [size] at ball
  have normed : (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out.size =
      s.width := by rw [(size_rmsNorm _ _ _ _).2, size]
  have norm := normOk_of_normFitsLength p.feedForwardBits p.feedForwardShift p.feedForwardEps x
    rowLength eps_pos length normFit
  cases mixture with
  | false =>
    simp only [feedForwardFitsInBall, Bool.false_eq_true, if_false] at fits
    simp only [feedForwardOk, feedForward, Bool.false_eq_true, if_false, Bool.and_eq_true]
    exact ⟨⟨⟨norm, hiddenUnits_fit_inBall tables w.shared s.width s.hidden p.gateShift p.upShift _ _
      normed box ball fits⟩, by simp [noRoute, fits16]⟩, by simp [noRoute, unitsOk, fits16]⟩
  | true =>
    simp only [feedForwardFitsInBall, if_true, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq]
      at fits
    simp only [feedForwardOk, feedForward, if_true, Bool.and_eq_true]
    have chosen := chosen_index s p tables w
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out (some_expert rfl)
    have inputBox := routedExpert_input_inBox s p tables w _ box routedFit
    have inputBall := routedExpert_input_inBall s p tables w _ _ box ball routedFit
    have inputSize : (routedExpert s p tables w
        (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).input.size =
        s.width := by rw [(size_routedExpert _ _ _ _ _).2.2.2.2, normed]
    exact ⟨⟨⟨norm, hiddenUnits_fit_inBall tables w.shared s.width s.expertHidden p.gateShift
      p.upShift _ _ normed box ball fits.1⟩,
      routedExpert_high_fits_inBall s p tables w _ _ normed box ball fun e he => (fits.2 e he).1⟩,
      hiddenUnits_fit_inBall tables (w.routed.entry _) s.width s.expertHidden p.routedGateShift
        p.routedUpShift _ _ inputSize inputBox inputBall (fits.2 _ chosen).2⟩

/-- All conditions of one layer at one position. -/
theorem length_layer_conditions (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : StretchNumbers) (l : Nat) (hl : l < s.layers) (X : Matrix)
    (formed : wellFormed s tables weights = true) (holds : numbers.Hold s weights)
    (routedFit : routedInputFits tables = true)
    (fits : lengthLayerFits s tables weights numbers l = true)
    (few : X.size ≤ s.positions) (rows : ∀ t, t < X.size → (X.entry t).size = s.width)
    (lengths : ∀ t, t < X.size →
      RowLengthWithin (streamLength s tables weights numbers l) (X.entry t))
    (t : Nat) (ht : t < X.size) :
    attentionOk (s.perLayer.entry l) (layer s tables weights l X).attention t = true
    ∧ feedForwardOk (s.perLayer.entry l) ((layer s tables weights l X).feedForward.entry t) =
      true := by
  simp only [lengthLayerFits, Bool.and_eq_true] at fits
  have parts := wellFormed_spec s tables weights formed
  have formedLayer := parts.2.2.2.2.2.2 l hl
  have eps := (layerWellFormed_spec _ _ _ _ formedLayer).2.2.2.2.1
  have shifts := layerWellFormed_shifts _ _ _ _ formedLayer
  have attended :=
    attention_out_length s tables weights numbers l hl X formed holds rows lengths t ht
  have size : ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry
      t).size = s.width := by
    rw [(size_attention_rows _ _ _ _ _ t ht).2.2.2]; exact rows t ht
  constructor
  · exact attentionOk_of_fitsInBall s (s.perLayer.entry l) tables (weights.perLayer.entry l) X _
      eps.1 shifts.1 few rows lengths fits.1.1.1 fits.1.1.2 t ht
  · rw [layer_feedForward_read s tables weights l X t ht]
    exact feedForwardOk_of_fitsInBall s (s.perLayer.entry l) tables (weights.perLayer.entry l)
      (s.isMixture l) _ _ (isMixture_experts s l) eps.2 shifts.2.2.1 size attended routedFit
      fits.1.2 fits.2

/-- **Weights that pass the length check with stretch numbers that hold never fail a range
condition.** For settings, tables and weights that fit together, all range conditions hold at all
positions of every prompt. -/
theorem allConditionsHold_of_lengthWorstCaseCheck (s : Settings) (tables : Tables)
    (weights : Weights) (numbers : StretchNumbers)
    (formed : wellFormed s tables weights = true)
    (holds : numbers.Hold s weights)
    (passes : lengthWorstCaseCheck s tables weights numbers = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) :
    allConditionsHold s (trace s tables weights prompt) = true := by
  simp only [lengthWorstCaseCheck, Bool.and_eq_true, allBelow_spec] at passes
  have parts := wellFormed_spec s tables weights formed
  have shape := embedded_shape s tables weights prompt formed prompt_ok
  have few := (isPrompt_spec s prompt prompt_ok).2.1
  have stream := fun l => stream_shape s tables weights
    (prompt.map fun token => weights.embedding.entry token) s.width l
    (fun t ht => shape.2 t (by rw [← shape.1]; exact ht))
  have lengths :=
    stream_length s tables weights numbers formed holds passes.1.1 prompt prompt_ok
  simp only [allConditionsHold, List.all_eq_true, List.mem_range, Bool.and_eq_true]
  intro t ht
  have ht' : t < prompt.size := by
    have : (trace s tables weights prompt).embedded.size = prompt.size := shape.1
    omega
  constructor
  · intro l hl
    have read : (trace s tables weights prompt).layer.entry l = layer s tables weights l
        (streamAbove (prompt.map fun token => weights.embedding.entry token)
          (firstLayers s tables weights (prompt.map fun token => weights.embedding.entry token)
            l)) := by
      simp only [trace]
      rw [firstLayers_read _ _ _ _ _ _ hl]
    rw [read]
    apply length_layer_conditions s tables weights numbers l hl _ formed holds passes.1.1
      (passes.1.2 l hl)
    · rw [(stream l).1, shape.1]; exact few
    · intro t ht
      exact (stream l).2 t (by rw [← (stream l).1]; exact ht)
    · intro t ht
      exact lengths l (by omega) t (by rw [← shape.1, ← (stream l).1]; exact ht)
    · rw [(stream l).1, shape.1]; exact ht'
  · have read : (trace s tables weights prompt).finalNorm.entry t =
        rmsNorm s.finalBits s.finalShift s.finalEps
          ((streamAbove (prompt.map fun token => weights.embedding.entry token)
            (firstLayers s tables weights (prompt.map fun token => weights.embedding.entry token)
              s.layers)).entry t) := by
      simp only [trace]
      rw [map_read _ _ _ (by rw [(stream s.layers).1, shape.1]; exact ht')]
    rw [read]
    exact normOk_of_normFitsLength _ _ _ _ _ parts.2.1.1
      (lengths s.layers (Nat.le_refl _) t ht') passes.2

/-- The Frobenius stretch numbers hold at all weights. -/
theorem frobeniusStretchNumbers_hold (s : Settings) (weights : Weights) :
    (frobeniusStretchNumbers s weights).Hold s weights :=
  fun _ _ =>
    ⟨stretchBound_frobenius _ _ _, stretchBound_frobenius _ _ _, stretchBound_frobenius _ _ _,
      fun _ _ _ => ⟨stretchBound_frobenius _ _ _, stretchBound_frobenius _ _ _⟩⟩

/-- The same with the Frobenius stretch numbers: beside `wellFormed`, the test is the only premise
on the weights. -/
theorem allConditionsHold_of_frobeniusLengthCheck (s : Settings) (tables : Tables)
    (weights : Weights) (formed : wellFormed s tables weights = true)
    (passes : lengthWorstCaseCheck s tables weights (frobeniusStretchNumbers s weights) = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) :
    allConditionsHold s (trace s tables weights prompt) = true :=
  allConditionsHold_of_lengthWorstCaseCheck s tables weights _ formed
    (frobeniusStretchNumbers_hold s weights) passes prompt prompt_ok

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.allConditionsHold_of_lengthWorstCaseCheck
#print axioms IntegerTransformer.Bounds.frobeniusStretchNumbers_hold
#print axioms IntegerTransformer.Bounds.allConditionsHold_of_frobeniusLengthCheck
