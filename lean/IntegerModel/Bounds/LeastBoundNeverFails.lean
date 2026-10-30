-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/LeastBoundNeverFails.lean

Weights that pass `leastBoundWorstCaseCheck` (IntegerModel/Bounds/LeastBoundCheck.lean) with numbers
that hold never fail a range condition. Five parts.
1. Conditions 3 to 7 for a vector in the box and the ball: `magnitude_rotate_product_le` over
   `pair_read_squares_le`; `projections_fit_leastBound`, `hiddenUnits_fit_leastBound`,
   `routedExpert_high_fits_leastBound`.
2. The addition after attention, in length: `value_head_length`, `head_out_length`,
   `mixed_length_leastBound`, `attention_addition_leastBound`.
3. The addition after a feed-forward block, in length: `activation_le_siluAt`,
   `stretched_hidden_length`, `stretch_scaled_columns`, `hidden_products_leastBound`,
   `downSum_length_leastBound`, `feedForward_addition_leastBound`.
4. Layers and the theorem. `stream_length_leastBound` is the induction over the layers: every row
   that enters layer `l` is at most `leastStreamLength .. l` long. It has no range condition among
   its premises. `allConditionsHold_of_leastBoundWorstCaseCheck`: for settings, tables and weights
   that fit together (`wellFormed`), numbers that hold and a check that passes, all range conditions
   hold at all positions of every prompt.
5. Numbers that need no hypothesis: Frobenius norms in every place, and for an up matrix with scaled
   columns the SiLU table's largest entry times the up matrix's Frobenius norm
   (`frobeniusLeastBoundNumbers_hold`). `allConditionsHold_of_frobeniusLeastBoundCheck` has, beside
   `wellFormed`, one premise on the settings, tables and weights, the value of a Boolean function.
Limits: those at the head of IntegerModel/Bounds/LeastBoundCheck.lean. The theorems go one way. This
file says of no weights and of no numbers that they pass. It imports Lean's core and the model's own
files.
-/
import IntegerModel.Bounds.LeastBoundCheck

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-! ## 1. Conditions 3 to 7 -/

/-- A read of a product, inside or outside, is no larger in square than the square of the column's
sum. -/
theorem product_read_square_le (a : IntegerVector) (W : Matrix) (outputs j : Nat) :
    (product a W outputs).entry j * (product a W outputs).entry j ≤
      (sumOver a.size fun k => a.entry k * (W.entry k).entry j)
        * (sumOver a.size fun k => a.entry k * (W.entry k).entry j) := by
  by_cases inside : j < outputs
  · unfold product
    rw [tabulate_read _ _ _ inside]
    exact Int.le_refl _
  · rw [entry_outside _ j (by rw [size_product]; exact inside)]
    exact square_nonneg _

/-- The squares of two neighbouring reads of a product are together within `pairSquaresBound`. -/
theorem pair_read_squares_le (taus : List Int) (a : IntegerVector) (W : Matrix) (outputs width : Nat)
    (fine : Ball) (size : a.size = width) (box : InBox a) (ball : InBall fine a)
    (first : Nat) :
    (product a W outputs).entry first * (product a W outputs).entry first
      + (product a W outputs).entry (first + 1) * (product a W outputs).entry (first + 1)
      ≤ pairSquaresBound taus fine W width first := by
  have b0 := square_le_square _ _
    (product_read_le_leastColumnBound taus a W outputs width fine size box ball first)
  have b1 := square_le_square _ _
    (product_read_le_leastColumnBound taus a W outputs width fine size box ball (first + 1))
  unfold pairSquaresBound
  dsimp only
  split
  · next dominates =>
    have s0 := product_read_square_le a W outputs first
    have s1 := product_read_square_le a W outputs (first + 1)
    have pair := pair_squares_le width (fun k => a.entry k) (fun k => (W.entry k).entry first)
      (fun k => (W.entry k).entry (first + 1)) (pairStretchSquare W width first) dominates.1
      dominates.2.1 dominates.2.2
    dsimp only at pair
    have nonneg : 0 ≤ pairStretchSquare W width first :=
      Int.le_trans (sumSquaresOver_nonneg _ _) dominates.1
    unfold InBall at ball
    rw [size] at ball s0 s1
    have length := ball.2
    rw [sumSquaresOver_scale] at length
    have scale : (0 : Int) < 2 ^ fine.shift * 2 ^ fine.shift :=
      Int.mul_pos (Int.pow_pos (by decide)) (Int.pow_pos (by decide))
    have scaled := Int.mul_le_mul_of_nonneg_left length nonneg
    have stretched := Int.mul_le_mul_of_nonneg_right pair (Int.le_of_lt scale)
    have fromBall : (sumOver width fun k => a.entry k * (W.entry k).entry first)
          * (sumOver width fun k => a.entry k * (W.entry k).entry first)
        + (sumOver width fun k => a.entry k * (W.entry k).entry (first + 1))
          * (sumOver width fun k => a.entry k * (W.entry k).entry (first + 1))
        ≤ pairStretchSquare W width first * (fine.numerator * fine.numerator)
          / (2 ^ fine.shift * 2 ^ fine.shift) := by
      apply (Int.le_ediv_iff_mul_le scale).mpr
      apply Int.le_trans stretched
      have e : pairStretchSquare W width first * (sumSquaresOver width fun k => a.entry k)
            * (2 ^ fine.shift * 2 ^ fine.shift) =
          pairStretchSquare W width first
            * (2 ^ fine.shift * 2 ^ fine.shift * sumSquaresOver width fun k => a.entry k) := by
              grind
      rw [e]
      exact scaled
    omega
  · omega

/-- **The rotary step.** An entry of a rotated product is within `leastRotatedBound`. -/
theorem magnitude_rotate_product_le (cosine sine : IntegerVector) (headDim : Nat) (taus : List Int) (a : IntegerVector)
    (W : Matrix) (outputs width : Nat) (fine : Ball) (size : a.size = width) (box : InBox a)
    (ball : InBall fine a) (j : Nat) (inside : j < outputs) :
    magnitude ((rotate cosine sine headDim (product a W outputs)).entry j) ≤
      leastRotatedBound cosine sine headDim taus fine W width j := by
  have first := magnitude_rotate_entry_le cosine sine headDim (product a W outputs) _
    (product_read_le_leastColumnBound taus a W outputs width fine size box ball) j
    (by rw [size_product]; exact inside)
  have second : magnitude ((rotate cosine sine headDim (product a W outputs)).entry j) ≤
      integerSquareRoot ((cosine.entry (j % headDim / 2) * cosine.entry (j % headDim / 2)
                    + sine.entry (j % headDim / 2) * sine.entry (j % headDim / 2))
                  * pairSquaresBound taus fine W width (j - j % 2)).toNat := by
    apply magnitude_le_isqrt
    have pair := pair_read_squares_le taus a W outputs width fine size box ball (j - j % 2)
    have turnNonneg : 0 ≤ cosine.entry (j % headDim / 2) * cosine.entry (j % headDim / 2)
        + sine.entry (j % headDim / 2) * sine.entry (j % headDim / 2) := by
      have := square_nonneg (cosine.entry (j % headDim / 2))
      have := square_nonneg (sine.entry (j % headDim / 2))
      omega
    have scaled := Int.mul_le_mul_of_nonneg_left pair turnNonneg
    apply Int.le_trans _ scaled
    unfold rotate
    rw [tabulate_read _ _ _ (by rw [size_product]; exact inside)]
    dsimp only
    split
    · next even =>
      have same : j - j % 2 = j := by omega
      rw [same]
      exact (turn_square_le _ _ _ _).1
    · next odd =>
      have same : j - j % 2 = j - 1 := by omega
      have next : j - 1 + 1 = j := by omega
      rw [same, next]
      exact (turn_square_le _ _ _ _).2
  unfold leastRotatedBound
  omega

/-- A product with an input in the box and the ball, shifted. -/
theorem shifted_read_le_leastColumnBound (taus : List Int) (z : IntegerVector) (W : Matrix)
    (outputs shift width j : Nat) (fine : Ball) (size : z.size = width) (box : InBox z)
    (ball : InBall fine z) (inside : j < outputs) :
    magnitude (((product z W outputs).map fun e => roundShift e shift).entry j) ≤
      roundShift (leastColumnBound taus fine W width j) shift := by
  rw [map_read _ _ _ (by rw [size_product]; exact inside)]
  exact magnitude_roundShift_le _ _ _
    (product_read_le_leastColumnBound taus z W outputs width fine size box ball j)

/-- A rotated and shifted product fits 16 bits, if its bounds do. -/
theorem rotated_fits_leastBound (cosine sine : IntegerVector) (headDim : Nat) (taus : List Int) (a : IntegerVector)
    (W : Matrix) (outputs width shift : Nat) (fine : Ball) (size : a.size = width) (box : InBox a)
    (ball : InBall fine a)
    (fits : ∀ j, j < outputs →
      roundShift (leastRotatedBound cosine sine headDim taus fine W width j) shift ≤ 32767) :
    fits16 ((rotate cosine sine headDim (product a W outputs)).map fun e => roundShift e
      shift) = true := by
  apply fits16_of_bounded _ 32767 _ (Int.le_refl _)
  intro j inside
  rw [Array.size_map, size_rotate, size_product] at inside
  rw [map_read _ _ _ (by rw [size_rotate, size_product]; exact inside)]
  apply Int.le_trans _ (fits j inside)
  apply magnitude_roundShift_le
  exact magnitude_rotate_product_le cosine sine headDim taus a W outputs width fine size box ball j
    inside

/-- Conditions 3 and 4 at one position, for a normed row in the box and the ball. -/
theorem projections_fit_leastBound (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (t : Nat) (a : IntegerVector) (taus : List Int) (fine : Ball)
    (position : t < s.positions) (size : a.size = s.width) (box : InBox a)
    (ball : InBall fine a)
    (fits : attentionFitsLeastBound s p tables w taus fine = true) :
    fits16 (projections s p tables w t a).wideQuery = true ∧
    fits16 (projections s p tables w t a).wideKey = true ∧
    fits16 (projections s p tables w t a).wideValue = true := by
  simp only [attentionFitsLeastBound, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq] at fits
  refine ⟨?_, ?_, ?_⟩
  · exact rotated_fits_leastBound (cosineRow s p tables t) (sineRow s p tables t) s.headDim taus a
      w.query s.queryWidth s.width p.queryShift fine size box ball (fits.1 t position).1
  · exact rotated_fits_leastBound (cosineRow s p tables t) (sineRow s p tables t) s.headDim taus a
      w.key s.keyValueWidth s.width p.keyShift fine size box ball (fits.1 t position).2
  · apply fits16_of_bounded _ 32767 _ (Int.le_refl _)
    intro j inside
    rw [(size_projections s p tables w t a).2.2.1] at inside
    exact Int.le_trans
      (shifted_read_le_leastColumnBound taus a w.value s.keyValueWidth p.valueShift s.width j fine
        size box ball inside)
      (fits.2 j inside)

/-- Conditions 6 and 7 of one gated block, for an input in the box and the ball. -/
theorem hiddenUnits_fit_leastBound (tables : Tables) (w : GatedWeights)
    (width hidden gateShift upShift : Nat) (z : IntegerVector) (taus : List Int) (fine : Ball)
    (size : z.size = width) (box : InBox z) (ball : InBall fine z)
    (fits : unitsFitLeastBound w width hidden gateShift upShift taus fine = true) :
    unitsOk (hiddenUnits tables w hidden gateShift upShift z) = true := by
  rw [unitsFitLeastBound, allBelow_spec] at fits
  have sizes := size_hiddenUnits tables w hidden gateShift upShift z
  simp only [unitsOk, Bool.and_eq_true]
  constructor
  · apply all_of_entries
    intro j inside
    rw [sizes.2.2.1] at inside
    have fit := fits j inside
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
    have gate := shifted_read_le_leastColumnBound taus z w.gate hidden gateShift width j fine size
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
      (shifted_read_le_leastColumnBound taus z w.up hidden upShift width j fine size
        box ball inside)
      fit.2

/-- Condition 5, for a normed row in the box and the ball. -/
theorem routedExpert_high_fits_leastBound (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (m : IntegerVector) (taus : List Int) (fine : Ball) (size : m.size = s.width)
    (box : InBox m) (ball : InBall fine m)
    (fits : ∀ e, e < s.experts →
      roundShift (leastColumnBound taus fine w.router s.width e) p.routerShift ≤ 262143) :
    fits16 (routedExpert s p tables w m).high = true := by
  have sizes := size_routedExpert s p tables w m
  unfold fits16
  apply all_of_entries
  intro e inside
  rw [sizes.2.1] at inside
  have wide := shifted_read_le_leastColumnBound taus m w.router s.experts p.routerShift s.width e
    fine size box ball inside
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

/-! ## 2. The addition after attention -/

/-- A vector within two lengths is within the smaller. -/
theorem length_min {n : Nat} {f : Nat → Int} {X Y : Int} (hX : LengthWithin n f X)
    (hY : LengthWithin n f Y) : LengthWithin n f (min X Y) := by
  rcases Int.le_total X Y with h | h
  · rw [Int.min_eq_left h]; exact hX
  · rw [Int.min_eq_right h]; exact hY

/-- A clamp makes no number larger in absolute value. -/
theorem magnitude_clamp_le_self (a b : Int) (h : 0 ≤ b) : magnitude (clamp a b) ≤ magnitude a := by
  unfold clamp magnitude; omega

/-- The value row of key-value head `g` at one position, in length. -/
theorem value_head_length (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (t : Nat) (a : IntegerVector) (taus : List Int) (fine : Ball) (stretch : Int) (g : Nat)
    (hg : g < s.keyValueHeads) (size : a.size = s.width) (box : InBox a)
    (ball : InBall fine a) (shift_pos : 1 ≤ p.valueShift)
    (bound : StretchBoundOf (fun row c => (w.value.entry row).entry (g * s.headDim + c)) s.width
      s.headDim stretch) :
    LengthWithin s.headDim (fun c => (projections s p tables w t a).value.entry (g * s.headDim + c))
      (valueHeadLength s p w taus fine stretch g) := by
  have valueAt : ∀ c, c < s.headDim → (projections s p tables w t a).value.entry
    (g * s.headDim + c) =
      clamp (roundShift ((product a w.value s.keyValueWidth).entry (g * s.headDim + c))
        p.valueShift)
        activationBound := by
    intro c hc
    have inside : g * s.headDim + c < s.keyValueWidth := head_index _ _ _ _ hg hc
    simp only [projections, map_read, size_product, Array.size_map, inside]
  unfold valueHeadLength
  apply length_min
  · apply length_of_bounds
    intro c hc
    rw [valueAt c hc]
    unfold valueEntryBound
    have h1 := magnitude_clamp_le (roundShift ((product a w.value s.keyValueWidth).entry
      (g * s.headDim + c)) p.valueShift) activationBound (by decide)
    have h2 := magnitude_clamp_le_self (roundShift ((product a w.value s.keyValueWidth).entry
      (g * s.headDim + c)) p.valueShift) activationBound (by decide)
    have h3 := magnitude_roundShift_le _ _ p.valueShift (product_read_le_leastColumnBound taus a
      w.value s.keyValueWidth s.width fine size box ball (g * s.headDim + c))
    omega
  · have whole := rowLength_of_inBall ball
    unfold RowLengthWithin at whole
    rw [size] at whole
    have rounded := length_roundShift (length_of_stretchBoundOf bound whole) p.valueShift shift_pos
    refine length_of_entries rounded fun c hc => ?_
    rw [valueAt c hc]
    have inside : g * s.headDim + c < s.keyValueWidth := head_index _ _ _ _ hg hc
    have read : (product a w.value s.keyValueWidth).entry (g * s.headDim + c) =
        sumOver s.width fun row => a.entry row * (w.value.entry row).entry (g * s.headDim + c) := by
      unfold product
      rw [tabulate_read _ _ _ inside, size]
    rw [read]
    exact clamp_square_le _ _ (by decide)

/-- One head's output, in length: a rounded mean of value rows. -/
theorem head_out_length (s : Settings) (p : LayerSettings) (tables : Tables)
    (projected : Array Projections) (i h : Nat) (V : Int)
    (values : ∀ j, j < i + 1 → LengthWithin s.headDim (fun c => (projected.entry j).value.entry
      (h / (s.queryHeads / s.keyValueHeads) * s.headDim + c)) V)
    (some_entry : 0 < tables.exponential.size) (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true) :
    LengthWithin s.headDim (fun c => (attendHead s p tables projected i h).out.entry c)
      (V + (rootUp s.headDim + 1) / 2) := by
  have positive := total_positive s p tables projected i h some_entry first none_negative
  have nonneg := exponentials_nonneg s p tables projected i h none_negative
  have made : (attendHead s p tables projected i h).out =
      (attendHead s p tables projected i h).mix.map fun acc =>
        (2 * acc + (attendHead s p tables projected i h).total) /
          (2 * (attendHead s p tables projected i h).total) := rfl
  have mixed : (attendHead s p tables projected i h).mix = tabulate s.headDim fun c =>
      sumOver (i + 1) fun j => (attendHead s p tables projected i h).exponentials.entry j *
        (projected.entry j).value.entry
          (h / (s.queryHeads / s.keyValueHeads) * s.headDim + c) := rfl
  have total : (attendHead s p tables projected i h).total =
      sumOver (i + 1) fun j => (attendHead s p tables projected i h).exponentials.entry j := rfl
  have size := (size_attendHead s p tables projected i h).2.1
  rw [total] at positive
  have mean := length_mean nonneg positive (values 0 (by omega)).1 values
  refine length_of_entries mean fun c inside => ?_
  rw [made, map_read _ _ _ (by rw [size]; exact inside), mixed, tabulate_read _ _ _ inside, total]
  exact Int.le_refl _

/-- Entry `c` of block `b`, for blocks of `m` entries: quotient and remainder of its index. -/
theorem block_index (m b c : Nat) (hc : c < m) : (b * m + c) / m = b ∧ (b * m + c) % m = c := by
  have positive : 0 < m := by omega
  rw [Nat.mul_comm b m]
  constructor
  · rw [Nat.mul_add_div positive, Nat.div_eq_of_lt hc, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

/-- All heads' outputs at one position, side by side, in length. -/
theorem mixed_length_leastBound (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights)
    (x : Matrix) (taus : List Int) (rowLength : Int) (stretchOf : Nat → Int)
    (divides : s.queryHeads % s.keyValueHeads = 0)
    (some_entry : 0 < tables.exponential.size) (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true)
    (eps_pos : 1 ≤ p.attentionEps) (norm_shift : 1 ≤ p.attentionShift)
    (value_shift : 1 ≤ p.valueShift)
    (rows : ∀ t, t < x.size → (x.entry t).size = s.width)
    (lengths : ∀ t, t < x.size → RowLengthWithin rowLength (x.entry t))
    (bounds : ∀ g, g < s.keyValueHeads →
      StretchBoundOf (fun row c => (w.value.entry row).entry (g * s.headDim + c))
        s.width s.headDim (stretchOf g))
    (t : Nat) (ht : t < x.size) :
    LengthWithin s.queryWidth (fun j => ((attention s p tables w x).mixed.entry t).entry j)
      (leastMixedLength s p w taus
        (normBall s.width p.attentionBits p.attentionShift p.attentionEps rowLength)
          stretchOf) := by
  have box := attention_mixed_inBox s p tables w x some_entry first none_negative t ht
  unfold leastMixedLength
  apply length_min
  · exact length_of_bounds (b := fun _ => activationBound) fun k _ => box k
  · unfold Settings.queryWidth
    apply length_of_blocks
    intro h hh
    have group := group_index s.queryHeads s.keyValueHeads h divides hh
    have out := head_out_length s p tables (attention s p tables w x).projected t h
      (valueHeadLength s p w taus
        (normBall s.width p.attentionBits p.attentionShift p.attentionEps rowLength)
        (stretchOf (h / (s.queryHeads / s.keyValueHeads))) (h / (s.queryHeads / s.keyValueHeads)))
      (fun i hi => by
        have inside : i < x.size := by omega
        have read : (attention s p tables w x).projected.entry i =
            projections s p tables w i
              (rmsNorm p.attentionBits p.attentionShift p.attentionEps (x.entry i)).out := by
          simp only [attention, tabulate_read, map_read, inside]
        rw [read]
        have ball := norm_out_inBall p.attentionBits p.attentionShift p.attentionEps (x.entry i)
          rowLength eps_pos norm_shift (lengths i inside)
        rw [rows i inside] at ball
        exact value_head_length s p tables w i _ taus _ _ _ group
          (by rw [(size_rmsNorm _ _ _ _).2, rows i inside]) (norm_out_inBox _ _ _ _) ball
            value_shift
          (bounds _ group))
      some_entry first none_negative
    refine length_of_entries out fun c hc => ?_
    have inside : h * s.headDim + c < s.queryWidth := head_index _ _ _ _ hh hc
    have index := block_index s.headDim h c hc
    have made : ((attention s p tables w x).mixed.entry t).entry (h * s.headDim + c) =
        (attendHead s p tables (attention s p tables w x).projected t h).out.entry c := by
      simp only [attention, tabulate_read, ht, inside, index.1, index.2, hh]
    rw [made]
    exact Int.le_refl _

/-- What attention adds to a row of the stream, in length. -/
theorem attention_addition_leastBound (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix) (taus : List Int) (rowLength : Int) (stretchOf : Nat → Int)
    (stretch : Int) (divides : s.queryHeads % s.keyValueHeads = 0)
    (some_entry : 0 < tables.exponential.size) (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true)
    (eps_pos : 1 ≤ p.attentionEps) (norm_shift : 1 ≤ p.attentionShift)
    (value_shift : 1 ≤ p.valueShift) (shift_pos : 1 ≤ p.outputShift)
    (rows : ∀ t, t < x.size → (x.entry t).size = s.width)
    (lengths : ∀ t, t < x.size → RowLengthWithin rowLength (x.entry t))
    (bounds : ∀ g, g < s.keyValueHeads →
      StretchBoundOf (fun row c => (w.value.entry row).entry (g * s.headDim + c))
        s.width s.headDim (stretchOf g))
    (bound : StretchBound w.output s.queryWidth s.width stretch) (t : Nat) (ht : t < x.size) :
    RowLengthWithin (leastAttentionAdditionLength s p w taus
        (normBall s.width p.attentionBits p.attentionShift p.attentionEps rowLength) stretchOf
          stretch)
      ((attention s p tables w x).addition.entry t) := by
  have size := (size_attention_rows s p tables w x t ht).2.1
  have made : (attention s p tables w x).addition.entry t =
      (product ((attention s p tables w x).mixed.entry t) w.output s.width).map
        fun e => roundShift e p.outputShift := by
    simp only [attention, map_read, size_tabulate, ht]
  have mixed := mixed_length_leastBound s p tables w x taus rowLength stretchOf divides some_entry
    first none_negative eps_pos norm_shift value_shift rows lengths bounds t ht
  have rounded := length_roundShift (length_of_stretchBound bound mixed) p.outputShift shift_pos
  unfold RowLengthWithin leastAttentionAdditionLength
  rw [made, Array.size_map, size_product]
  refine length_of_entries rounded fun k inside => ?_
  rw [map_read _ _ _ (by rw [size_product]; exact inside)]
  unfold product
  rw [tabulate_read _ _ _ inside, size]
  exact Int.le_refl _

/-! ## 3. The addition after a feed-forward block -/

/-- `siluAt` bounds the activation of hidden unit `j`. -/
theorem activation_le_siluAt (tables : Tables) (w : GatedWeights)
    (width hidden gateShift upShift : Nat) (z : IntegerVector) (taus : List Int) (fine : Ball)
    (size : z.size = width) (box : InBox z) (ball : InBall fine z) (j : Nat)
    (inside : j < hidden) :
    magnitude ((hiddenUnits tables w hidden gateShift upShift z).activation.entry j) ≤
      siluAt tables w width gateShift taus fine j := by
  have sizes := size_hiddenUnits tables w hidden gateShift upShift z
  have made : (hiddenUnits tables w hidden gateShift upShift z).activation =
      (hiddenUnits tables w hidden gateShift upShift z).key.map tables.silu.read := rfl
  rw [made, map_read _ _ _ (by rw [sizes.2.2.2.2.1]; exact inside),
    hiddenUnits_key tables w hidden gateShift upShift z j inside]
  apply magnitude_silu_read_le
  have wide : magnitude ((hiddenUnits tables w hidden gateShift upShift z).wideGate.entry j) ≤
      roundShift (leastColumnBound taus fine w.gate width j) gateShift :=
    shifted_read_le_leastColumnBound taus z w.gate hidden gateShift width j fine size
      box ball inside
  have key := magnitude_gateKeyOf_le ((hiddenUnits tables w hidden gateShift upShift
    z).wideGate.entry j)
  unfold gateReach
  omega

/-- The up projection of hidden unit `j`, as a rounded sum. -/
theorem up_read (tables : Tables) (w : GatedWeights) (width hidden gateShift upShift : Nat)
    (z : IntegerVector) (size : z.size = width) (j : Nat) (inside : j < hidden) :
    (hiddenUnits tables w hidden gateShift upShift z).up.entry j =
      roundShift (sumOver width fun row => z.entry row * (w.up.entry row).entry j) upShift := by
  simp only [hiddenUnits, product, map_read, tabulate_read, size_tabulate, inside, size]

/-- The products of activation and up projection, by a stretch of the up matrix with scaled columns.
-/
theorem stretched_hidden_length (tables : Tables) (w : GatedWeights)
    (width hidden gateShift upShift : Nat) (z : IntegerVector) (taus : List Int) (fine : Ball) (stretch : Int)
    (size : z.size = width) (shift_pos : 1 ≤ upShift) (box : InBox z)
    (ball : InBall fine z)
    (bound : StretchBoundOf (scaledUpEntries tables w width gateShift taus fine) width hidden
      stretch) :
    LengthWithin hidden
      (fun j => (hiddenUnits tables w hidden gateShift upShift z).activation.entry j
        * (hiddenUnits tables w hidden gateShift upShift z).up.entry j)
      (stretchedHiddenLength (siluAt tables w width gateShift taus fine) hidden upShift stretch
        fine.radius) := by
  have activation := activation_le_siluAt tables w width hidden gateShift upShift z taus fine size
    box ball
  have up := up_read tables w width hidden gateShift upShift z size
  have pos : (0 : Int) < 2 ^ upShift := Int.pow_pos (by decide)
  have half : (0 : Int) < 2 ^ (upShift - 1) := Int.pow_pos (by decide)
  have ballAt : LengthWithin width (fun k => z.entry k) fine.radius := by
    have whole := rowLength_of_inBall ball
    unfold RowLengthWithin at whole
    rw [size] at whole
    exact whole
  generalize (hiddenUnits tables w hidden gateShift upShift z).activation = act at *
  generalize (hiddenUnits tables w hidden gateShift upShift z).up = u at *
  generalize hS : siluAt tables w width gateShift taus fine = S at *
  -- the products with the sums before their rounding
  have stretched := length_of_stretchBoundOf bound ballAt
  have first : LengthWithin hidden
      (fun j => act.entry j * sumOver width fun row => z.entry row * (w.up.entry row).entry j)
      (stretch * fine.radius) := by
    refine length_of_entries stretched fun j inside => ?_
    have scaled : (sumOver width fun row => z.entry row
        * scaledUpEntries tables w width gateShift taus fine row j) =
        S j * sumOver width fun row => z.entry row * (w.up.entry row).entry j := by
      rw [← sumOver_mul_left]
      unfold scaledUpEntries
      rw [hS]
      congr 1
      funext row
      grind
    rw [scaled]
    generalize (sumOver width fun row => z.entry row * (w.up.entry row).entry j) = P
    have square := Int.mul_le_mul_of_nonneg_right (square_le_square _ _ (activation j inside))
      (square_nonneg P)
    have e1 : act.entry j * P * (act.entry j * P) = act.entry j * act.entry j * (P * P) := by grind
    have e2 : S j * P * (S j * P) = S j * S j * (P * P) := by grind
    omega
  -- what the rounding of the up projection adds
  have lengthS : LengthWithin hidden S (rootUp (sumSquaresOver hidden S)) :=
    ⟨(rootUp_spec _).1, (rootUp_spec _).2⟩
  have second : LengthWithin hidden
      (fun j => act.entry j * (2 ^ upShift * u.entry j
        - sumOver width fun row => z.entry row * (w.up.entry row).entry j))
      (2 ^ (upShift - 1) * rootUp (sumSquaresOver hidden S)) := by
    refine length_of_entries (length_scale lengthS (by omega)) fun j inside => ?_
    rw [up j inside]
    have error := roundShift_error
      (sumOver width fun row => z.entry row * (w.up.entry row).entry j) upShift shift_pos
    have both := magnitude_mul_le_mul _ _ _ _ (activation j inside) error
    have square := square_le_square _ _ both
    have e : S j * 2 ^ (upShift - 1) * (S j * 2 ^ (upShift - 1)) =
        2 ^ (upShift - 1) * S j * (2 ^ (upShift - 1) * S j) := by grind
    omega
  have sum := length_add first second
  have same : (fun j => act.entry j
    * (sumOver width fun row => z.entry row * (w.up.entry row).entry j)
      + act.entry j * (2 ^ upShift * u.entry j
        - sumOver width fun row => z.entry row * (w.up.entry row).entry j)) =
      fun j => 2 ^ upShift * (act.entry j * u.entry j) := by
    funext j
    grind
  rw [same] at sum
  unfold stretchedHiddenLength
  exact length_unscale pos (shiftUp_nonneg sum.1 upShift) (length_of_le sum (shiftUp_spec _ _))

/-- The up matrix with scaled columns stretches by at most the SiLU table's largest entry times the
stretch of the up matrix. -/
theorem stretch_scaled_columns (tables : Tables) (w : GatedWeights) (width hidden gateShift : Nat)
    (taus : List Int) (fine : Ball) (stretch : Int)
      (bound : StretchBound w.up width hidden stretch) :
    StretchBoundOf (scaledUpEntries tables w width gateShift taus fine) width hidden
      (largestMagnitude tables.silu.entries * stretch) := by
  have largest : 0 ≤ largestMagnitude tables.silu.entries :=
    Int.le_trans (siluBoundWithin_nonneg tables 0) (siluBoundWithin_le_largest tables 0)
  refine ⟨Int.mul_nonneg largest bound.1, fun v => ?_⟩
  have plain := bound.2 v
  have each : sumSquaresOver hidden (fun column => sumOver width fun row =>
        v row * scaledUpEntries tables w width gateShift taus fine row column)
      ≤ sumOver hidden fun column =>
        largestMagnitude tables.silu.entries * largestMagnitude tables.silu.entries
          * ((sumOver width fun row => v row * (w.up.entry row).entry column)
            * (sumOver width fun row => v row * (w.up.entry row).entry column)) := by
    refine sumOver_le_sumOver _ _ _ fun column _ => ?_
    have scaled : (sumOver width fun row => v row
        * scaledUpEntries tables w width gateShift taus fine row column) =
        siluAt tables w width gateShift taus fine column
          * sumOver width fun row => v row * (w.up.entry row).entry column := by
      rw [← sumOver_mul_left]
      unfold scaledUpEntries
      congr 1
      funext row
      grind
    dsimp only
    rw [scaled]
    have small : magnitude (siluAt tables w width gateShift taus fine column) ≤
        largestMagnitude tables.silu.entries := by
      have nonneg := siluBoundWithin_nonneg tables
        (gateReach (leastColumnBound taus fine w.gate width column) gateShift)
      have le := siluBoundWithin_le_largest tables
        (gateReach (leastColumnBound taus fine w.gate width column) gateShift)
      unfold siluAt magnitude
      omega
    generalize siluAt tables w width gateShift taus fine column = S at *
    generalize (sumOver width fun row => v row * (w.up.entry row).entry column) = P
    have square := Int.mul_le_mul_of_nonneg_right (square_le_square _ _ small) (square_nonneg P)
    have e : S * P * (S * P) = S * S * (P * P) := by grind
    omega
  rw [sumOver_mul_left] at each
  have scaledPlain := Int.mul_le_mul_of_nonneg_left plain
    (square_nonneg (largestMagnitude tables.silu.entries))
  unfold sumSquaresOver at scaledPlain each ⊢
  have e : largestMagnitude tables.silu.entries * stretch
        * (largestMagnitude tables.silu.entries * stretch) * (sumOver width fun k => v k * v k) =
      largestMagnitude tables.silu.entries * largestMagnitude tables.silu.entries
        * (stretch * stretch * sumOver width fun k => v k * v k) := by grind
  rw [e]
  exact Int.le_trans each scaledPlain

/-- The products of activation and up projection of one block, in length: the least of four bounds.
-/
theorem hidden_products_leastBound (tables : Tables) (w : GatedWeights)
    (width hidden gateShift upShift : Nat) (z : IntegerVector) (taus : List Int)
    (fine : Ball) (stretchUp stretchScaledUp : Int) (size : z.size = width)
      (shift_pos : 1 ≤ upShift)
    (box : InBox z) (ball : InBall fine z)
    (boundUp : StretchBound w.up width hidden stretchUp)
    (boundScaled : StretchBoundOf (scaledUpEntries tables w width gateShift taus fine) width hidden
      stretchScaledUp) :
    LengthWithin hidden
      (fun j => (hiddenUnits tables w hidden gateShift upShift z).activation.entry j
        * (hiddenUnits tables w hidden gateShift upShift z).up.entry j)
      (leastHiddenLength tables w width hidden gateShift upShift taus fine stretchUp
        stretchScaledUp) := by
  unfold leastHiddenLength
  apply length_min
  · apply length_min
    · exact hidden_products_length tables w width hidden gateShift upShift z fine.radius stretchUp
        size shift_pos (rowLength_of_inBall ball) boundUp
    · apply length_of_bounds
      intro j inside
      apply magnitude_mul_le_mul
      · exact activation_le_siluAt tables w width hidden gateShift upShift z taus fine size box ball
          j inside
      · exact shifted_read_le_leastColumnBound taus z w.up hidden upShift width j fine size box ball
          inside
  · apply length_min
    · exact stretched_hidden_length tables w width hidden gateShift upShift z taus fine _ size
        shift_pos box ball boundScaled
    · exact stretched_hidden_length tables w width hidden gateShift upShift z taus fine _ size
        shift_pos box ball (stretch_scaled_columns tables w width hidden gateShift taus fine _
          boundUp)

/-- One block's down projection before the shift, in length. -/
theorem downSum_length_leastBound (tables : Tables) (w : GatedWeights)
    (width hidden gateShift upShift : Nat) (z : IntegerVector) (taus : List Int)
    (fine : Ball) (stretchUp stretchScaledUp stretchDown : Int) (size : z.size = width)
    (shift_pos : 1 ≤ upShift) (box : InBox z) (ball : InBall fine z)
    (holds : GatedStretchNumbersHold tables w width hidden gateShift taus fine stretchUp
      stretchScaledUp stretchDown) :
    LengthWithin width (fun k => downSum (hiddenUnits tables w hidden gateShift upShift z) w.down k)
      (stretchDown * leastHiddenLength tables w width hidden gateShift upShift taus fine
        stretchUp stretchScaledUp) := by
  have sizes := size_hiddenUnits tables w hidden gateShift upShift z
  have products := hidden_products_leastBound tables w width hidden gateShift upShift z taus fine
    stretchUp stretchScaledUp size shift_pos box ball holds.1 holds.2.1
  have stretched := length_of_stretchBound holds.2.2 products
  refine length_of_entries stretched fun k _ => ?_
  unfold downSum
  rw [sizes.2.2.2.2.2.2]
  exact Int.le_refl _

/-- What the feed-forward block of layer `l` adds to a row of the stream, in length. -/
theorem feedForward_addition_leastBound (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) (l : Nat)
    (formedLayer : layerWellFormed s (s.perLayer.entry l) (weights.perLayer.entry l)
      (s.isMixture l) = true)
    (routedFit : routedInputFits tables = true)
    (x : IntegerVector) (X : Int) (size : x.size = s.width) (h : RowLengthWithin X x)
    (shared : GatedStretchNumbersHold tables (weights.perLayer.entry l).shared s.width
      (sharedHidden s l) (s.perLayer.entry l).gateShift numbers.taus (feedForwardBall s l X)
      (numbers.up l) (numbers.scaledUp l) (numbers.down l))
    (routed : s.isMixture l = true → ∀ e, e < s.experts →
      GatedStretchNumbersHold tables ((weights.perLayer.entry l).routed.entry e) s.width
        s.expertHidden (s.perLayer.entry l).routedGateShift numbers.taus (feedForwardBall s l X)
        (numbers.routedUp l e) (numbers.routedScaledUp l e) (numbers.routedDown l e)) :
    RowLengthWithin (leastFeedForwardAdditionLength s tables weights numbers l (feedForwardBall s l
      X)) (feedForward s (s.perLayer.entry l) tables (weights.perLayer.entry l) (s.isMixture l)
        x).addition := by
  have eps_pos := (layerWellFormed_spec _ _ _ _ formedLayer).2.2.2.2.1.2
  have shifts := layerWellFormed_shifts _ _ _ _ formedLayer
  unfold RowLengthWithin leastFeedForwardAdditionLength
  unfold feedForwardBall at *
  rw [(size_feedForward _ _ _ _ _ _).1]
  unfold sharedHidden at shared
  dsimp only
  generalize s.perLayer.entry l = p at *
  generalize weights.perLayer.entry l = w at *
  have box := norm_out_inBox p.feedForwardBits p.feedForwardShift p.feedForwardEps x
  have normed : (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out.size =
      s.width := by rw [(size_rmsNorm _ _ _ _).2, size]
  have ball := norm_out_inBall p.feedForwardBits p.feedForwardShift p.feedForwardEps x X eps_pos
    shifts.2.2.1 h
  rw [size] at ball
  generalize normBall s.width p.feedForwardBits p.feedForwardShift p.feedForwardEps X = fine at *
  by_cases mixture : s.isMixture l = true
  · simp only [mixture, if_true] at shared ⊢
    have some_expert := isMixture_experts s l mixture
    have chosen := chosen_index s p tables w
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out some_expert
    have inputBox := routedExpert_input_inBox s p tables w _ box routedFit
    have inputBall := routedExpert_input_inFineBall s p tables w _ fine box ball routedFit
    have inputSize : (routedExpert s p tables w
        (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).input.size =
        s.width := by rw [(size_routedExpert _ _ _ _ _).2.2.2.2, normed]
    have sharedLength := downSum_length_leastBound tables w.shared s.width s.expertHidden
      p.gateShift p.upShift _ numbers.taus fine _ _ _ normed shifts.2.2.2.1 box ball shared
    have routedLength := downSum_length_leastBound tables (w.routed.entry _) s.width s.expertHidden
      p.routedGateShift p.routedUpShift _ numbers.taus fine _ _ _ inputSize
      (shifts.2.2.2.2.2 mixture) inputBox inputBall (routed mixture _ chosen)
    have largest := length_of_le routedLength ((maxUpTo_spec (fun e => numbers.routedDown l e
      * leastHiddenLength tables (w.routed.entry e) s.width s.expertHidden p.routedGateShift
        p.routedUpShift numbers.taus fine (numbers.routedUp l e)
        (numbers.routedScaledUp l e)) (s.experts - 1)).1 _ (by omega))
    have rounded := length_roundShift (length_add sharedLength largest) p.downShift shifts.2.2.2.2.1
    refine length_of_entries rounded fun k inside => ?_
    simp only [feedForward, if_true, tabulate_read, inside]
    exact Int.le_refl _
  · have dense : s.isMixture l = false := by simpa using mixture
    simp only [dense, Bool.false_eq_true, if_false] at shared ⊢
    have sharedLength := downSum_length_leastBound tables w.shared s.width s.hidden p.gateShift
      p.upShift _ numbers.taus fine _ _ _ normed shifts.2.2.2.1 box ball shared
    have rounded := length_roundShift sharedLength p.downShift shifts.2.2.2.2.1
    refine length_of_entries rounded fun k inside => ?_
    simp only [feedForward, Bool.false_eq_true, if_false, tabulate_read, inside]
    exact Int.le_refl _

/-! ## 4. Layers, the induction, the theorem -/

/-- The value shift of a well-formed layer is at least 1. -/
theorem layerWellFormed_valueShift (s : Settings) (p : LayerSettings) (w : LayerWeights)
    (mixture : Bool) (h : layerWellFormed s p w mixture = true) : 1 ≤ p.valueShift := by
  simp only [layerWellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, v⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact v

/-- The stream after attention, in length. -/
theorem attention_out_leastBound (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) (l : Nat) (hl : l < s.layers) (X : Matrix)
    (formed : wellFormed s tables weights = true) (holds : numbers.Hold s tables weights)
    (rows : ∀ t, t < X.size → (X.entry t).size = s.width)
    (lengths : ∀ t, t < X.size →
      RowLengthWithin (leastStreamLength s tables weights numbers l) (X.entry t))
    (t : Nat) (ht : t < X.size) :
    RowLengthWithin (leastStreamLengthAfterAttention s tables weights numbers l)
      ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry t) := by
  have parts := wellFormed_spec s tables weights formed
  have formedLayer := parts.2.2.2.2.2.2 l hl
  have shifts := layerWellFormed_shifts _ _ _ _ formedLayer
  have eps := (layerWellFormed_spec _ _ _ _ formedLayer).2.2.2.2.1
  have made : (attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry t
      = addVectors (X.entry t)
        ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).addition.entry
          t) := by
    simp only [attention, tabulate_read, ht]
  rw [made]
  apply addVec_length _ _ _ _ _ (lengths t ht)
  · exact attention_addition_leastBound s _ tables _ X numbers.taus _ (numbers.valueHead l) _
      parts.1.2.2.1 parts.2.2.1.2.2.1 parts.2.2.1.2.2.2.1 parts.2.2.1.2.2.2.2.1 eps.1 shifts.1
      (layerWellFormed_valueShift _ _ _ _ formedLayer) shifts.2.1 rows lengths (holds l hl).2.1
      (holds l hl).1 t ht
  · rw [(size_attention_rows _ _ _ _ _ t ht).2.2.1, rows t ht]

/-- One layer's step on the stream's length. -/
theorem layer_out_leastBound (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) (l : Nat) (hl : l < s.layers) (X : Matrix)
    (formed : wellFormed s tables weights = true) (holds : numbers.Hold s tables weights)
    (routedFit : routedInputFits tables = true)
    (rows : ∀ t, t < X.size → (X.entry t).size = s.width)
    (lengths : ∀ t, t < X.size →
      RowLengthWithin (leastStreamLength s tables weights numbers l) (X.entry t))
    (t : Nat) (ht : t < X.size) :
    RowLengthWithin (leastStreamLength s tables weights numbers (l + 1))
      ((layer s tables weights l X).out.entry t) := by
  have parts := wellFormed_spec s tables weights formed
  have attended := attention_out_leastBound s tables weights numbers l hl X formed holds rows
    lengths t ht
  have size : ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry
      t).size = s.width := by
    rw [(size_attention_rows _ _ _ _ _ t ht).2.2.2]; exact rows t ht
  rw [layer_out_read s tables weights l X t ht, feedForward_out]
  apply addVec_length _ _ _ _ _ attended
  · exact feedForward_addition_leastBound s tables weights numbers l (parts.2.2.2.2.2.2 l hl)
      routedFit _ _ size attended (holds l hl).2.2.1 (holds l hl).2.2.2
  · rw [(size_feedForward _ _ _ _ _ _).1, size]

/-- **The induction.** Every row that enters layer `l` is at most `leastStreamLength .. l` long. No
range condition is among its premises. -/
theorem stream_length_leastBound (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) (formed : wellFormed s tables weights = true)
    (holds : numbers.Hold s tables weights) (routedFit : routedInputFits tables = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) (l : Nat) (hl : l ≤ s.layers)
    (t : Nat) (ht : t < prompt.size) :
    RowLengthWithin (leastStreamLength s tables weights numbers l)
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
    apply layer_out_leastBound s tables weights numbers l (by omega) _ formed holds routedFit
    · intro t ht
      exact stream.2 t (by rw [← stream.1]; exact ht)
    · intro t ht
      exact ih (by omega) t (by rw [← shape.1, ← stream.1]; exact ht)
    · rw [stream.1, shape.1]; exact ht

/-- Conditions 1 to 4 at one position of one layer. -/
theorem attentionOk_of_fitsLeastBound (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix) (taus : List Int) (rowLength : Int)
      (eps_pos : 1 ≤ p.attentionEps)
    (shift_pos : 1 ≤ p.attentionShift)
    (few : x.size ≤ s.positions) (rows : ∀ t, t < x.size → (x.entry t).size = s.width)
    (lengths : ∀ t, t < x.size → RowLengthWithin rowLength (x.entry t))
    (normFit : normFitsLength p.attentionBits p.attentionShift p.attentionEps rowLength = true)
    (fits : attentionFitsLeastBound s p tables w taus
      (normBall s.width p.attentionBits p.attentionShift p.attentionEps rowLength) = true)
    (t : Nat) (ht : t < x.size) :
    attentionOk p (attention s p tables w x) t = true := by
  have norm : (attention s p tables w x).norm.entry t =
      rmsNorm p.attentionBits p.attentionShift p.attentionEps (x.entry t) := by
    simp only [attention, map_read, ht]
  have read : (attention s p tables w x).projected.entry t =
      projections s p tables w t ((attention s p tables w x).norm.entry t).out := by
    simp only [attention, tabulate_read, ht]
  have ball := norm_out_inBall p.attentionBits p.attentionShift p.attentionEps (x.entry t) rowLength
    eps_pos shift_pos (lengths t ht)
  rw [rows t ht] at ball
  have parts := projections_fit_leastBound s p tables w t
    (rmsNorm p.attentionBits p.attentionShift p.attentionEps (x.entry t)).out taus _ (by omega)
    (by rw [(size_rmsNorm _ _ _ _).2, rows t ht]) (norm_out_inBox _ _ _ _) ball fits
  simp only [attentionOk, Bool.and_eq_true]
  rw [read, norm]
  exact ⟨⟨⟨normOk_of_normFitsLength _ _ _ _ rowLength eps_pos (lengths t ht) normFit,
    parts.1⟩, parts.2.1⟩, parts.2.2⟩

/-- Conditions 1, 2, 5, 6 and 7 of one layer's feed-forward block at one position. -/
theorem feedForwardOk_of_fitsLeastBound (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (mixture : Bool) (x : IntegerVector) (taus : List Int) (rowLength : Int)
    (some_expert : mixture = true → 0 < s.experts) (eps_pos : 1 ≤ p.feedForwardEps)
    (shift_pos : 1 ≤ p.feedForwardShift)
    (size : x.size = s.width) (length : RowLengthWithin rowLength x)
    (routedFit : routedInputFits tables = true)
    (normFit : normFitsLength p.feedForwardBits p.feedForwardShift p.feedForwardEps
      rowLength = true)
    (fits : feedForwardFitsLeastBound s p w mixture taus
      (normBall s.width p.feedForwardBits p.feedForwardShift p.feedForwardEps rowLength) = true) :
    feedForwardOk p (feedForward s p tables w mixture x) = true := by
  have box := norm_out_inBox p.feedForwardBits p.feedForwardShift p.feedForwardEps x
  have ball := norm_out_inBall p.feedForwardBits p.feedForwardShift p.feedForwardEps x rowLength
    eps_pos shift_pos length
  rw [size] at ball
  have normed : (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out.size =
      s.width := by rw [(size_rmsNorm _ _ _ _).2, size]
  have norm := normOk_of_normFitsLength p.feedForwardBits p.feedForwardShift p.feedForwardEps x
    rowLength eps_pos length normFit
  cases mixture with
  | false =>
    simp only [feedForwardFitsLeastBound, Bool.false_eq_true, if_false] at fits
    simp only [feedForwardOk, feedForward, Bool.false_eq_true, if_false, Bool.and_eq_true]
    exact ⟨⟨⟨norm, hiddenUnits_fit_leastBound tables w.shared s.width s.hidden p.gateShift
      p.upShift _ taus _ normed box ball fits⟩, by simp [noRoute, fits16]⟩,
      by simp [noRoute, unitsOk, fits16]⟩
  | true =>
    simp only [feedForwardFitsLeastBound, if_true, Bool.and_eq_true, allBelow_spec,
      decide_eq_true_eq] at fits
    simp only [feedForwardOk, feedForward, if_true, Bool.and_eq_true]
    have chosen := chosen_index s p tables w
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out (some_expert rfl)
    have inputBox := routedExpert_input_inBox s p tables w _ box routedFit
    have inputBall := routedExpert_input_inFineBall s p tables w _ _ box ball routedFit
    have inputSize : (routedExpert s p tables w
        (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).input.size =
        s.width := by rw [(size_routedExpert _ _ _ _ _).2.2.2.2, normed]
    exact ⟨⟨⟨norm, hiddenUnits_fit_leastBound tables w.shared s.width s.expertHidden p.gateShift
      p.upShift _ taus _ normed box ball fits.1⟩,
      routedExpert_high_fits_leastBound s p tables w _ taus _ normed box ball
        fun e he => (fits.2 e he).1⟩,
      hiddenUnits_fit_leastBound tables (w.routed.entry _) s.width s.expertHidden p.routedGateShift
        p.routedUpShift _ taus _ inputSize inputBox inputBall (fits.2 _ chosen).2⟩

/-- All conditions of one layer at one position, from the layer's check and the stream's length. -/
theorem leastBound_layer_conditions (s : Settings) (tables : Tables) (weights : Weights)
    (numbers : LeastBoundNumbers) (l : Nat) (hl : l < s.layers) (X : Matrix)
    (formed : wellFormed s tables weights = true) (holds : numbers.Hold s tables weights)
    (routedFit : routedInputFits tables = true)
    (fits : leastBoundLayerFits s tables weights numbers l = true)
    (few : X.size ≤ s.positions) (rows : ∀ t, t < X.size → (X.entry t).size = s.width)
    (lengths : ∀ t, t < X.size →
      RowLengthWithin (leastStreamLength s tables weights numbers l) (X.entry t))
    (t : Nat) (ht : t < X.size) :
    attentionOk (s.perLayer.entry l) (layer s tables weights l X).attention t = true
    ∧ feedForwardOk (s.perLayer.entry l)
      ((layer s tables weights l X).feedForward.entry t) = true := by
  simp only [leastBoundLayerFits, Bool.and_eq_true] at fits
  have parts := wellFormed_spec s tables weights formed
  have formedLayer := parts.2.2.2.2.2.2 l hl
  have eps := (layerWellFormed_spec _ _ _ _ formedLayer).2.2.2.2.1
  have shifts := layerWellFormed_shifts _ _ _ _ formedLayer
  have attended := attention_out_leastBound s tables weights numbers l hl X formed holds rows
    lengths t ht
  have size : ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry
      t).size = s.width := by
    rw [(size_attention_rows _ _ _ _ _ t ht).2.2.2]; exact rows t ht
  constructor
  · exact attentionOk_of_fitsLeastBound s (s.perLayer.entry l) tables (weights.perLayer.entry l) X
      numbers.taus _ eps.1 shifts.1 few rows lengths fits.1.1.1 fits.1.1.2 t ht
  · rw [layer_feedForward_read s tables weights l X t ht]
    exact feedForwardOk_of_fitsLeastBound s (s.perLayer.entry l) tables (weights.perLayer.entry l)
      (s.isMixture l) _ numbers.taus _ (isMixture_experts s l) eps.2 shifts.2.2.1 size attended
      routedFit fits.1.2 fits.2

/-- **Weights that pass the least-bound check with numbers that hold never fail a range condition.**
For settings, tables and weights that fit together, all range conditions hold at all positions of
every prompt. -/
theorem allConditionsHold_of_leastBoundWorstCaseCheck (s : Settings) (tables : Tables)
    (weights : Weights) (numbers : LeastBoundNumbers)
    (formed : wellFormed s tables weights = true)
    (holds : numbers.Hold s tables weights)
    (passes : leastBoundWorstCaseCheck s tables weights numbers = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) :
    allConditionsHold s (trace s tables weights prompt) = true := by
  simp only [leastBoundWorstCaseCheck, Bool.and_eq_true, allBelow_spec] at passes
  have parts := wellFormed_spec s tables weights formed
  have shape := embedded_shape s tables weights prompt formed prompt_ok
  have few := (isPrompt_spec s prompt prompt_ok).2.1
  have stream := fun l => stream_shape s tables weights
    (prompt.map fun token => weights.embedding.entry token) s.width l
    (fun t ht => shape.2 t (by rw [← shape.1]; exact ht))
  have lengths := stream_length_leastBound s tables weights numbers formed holds passes.1.1 prompt
    prompt_ok
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
    apply leastBound_layer_conditions s tables weights numbers l hl _ formed holds passes.1.1
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
    exact normOk_of_normFitsLength _ _ _ _ _ parts.2.1.1 (lengths s.layers (Nat.le_refl _) t ht')
      passes.2

/-! ## 5. Numbers that need no hypothesis -/

/-- At or above the Frobenius norm of a matrix that is given by its entries. -/
def frobeniusStretchOf (entries : Nat → Nat → Int) (rows columns : Nat) : Int :=
  rootUp (sumOver columns fun column => sumSquaresOver rows fun row => entries row column)

/-- The Frobenius norm bounds the stretch: Cauchy-Schwarz for each column. -/
theorem stretchBoundOf_frobenius (entries : Nat → Nat → Int) (rows columns : Nat) :
    StretchBoundOf entries rows columns (frobeniusStretchOf entries rows columns) := by
  have root := rootUp_spec
    (sumOver columns fun column => sumSquaresOver rows fun row => entries row column)
  refine ⟨root.1, fun v => ?_⟩
  unfold frobeniusStretchOf
  have each : sumSquaresOver columns
    (fun column => sumOver rows fun row => v row * entries row column)
      ≤ sumOver columns fun column =>
        sumSquaresOver rows v * sumSquaresOver rows fun row => entries row column :=
    sumOver_le_sumOver _ _ _ fun column _ => cauchy_schwarz rows v fun row => entries row column
  rw [sumOver_mul_left] at each
  have scaled := Int.mul_le_mul_of_nonneg_left root.2 (sumSquaresOver_nonneg rows v)
  rw [Int.mul_comm (sumSquaresOver rows v) (_ * _)] at scaled
  exact Int.le_trans each scaled

/-- Frobenius norms in every place; for an up matrix with scaled columns the SiLU table's largest
entry times that of the up matrix. -/
def frobeniusLeastBoundNumbers (settings : Settings) (tables : Tables) (weights : Weights)
    (taus : List Int) : LeastBoundNumbers where
  taus := taus
  output layer :=
    frobeniusStretch (weights.perLayer.entry layer).output settings.queryWidth settings.width
  valueHead layer keyValueHead :=
    frobeniusStretchOf
      (fun row coordinate => ((weights.perLayer.entry layer).value.entry row).entry
        (keyValueHead * settings.headDim + coordinate))
      settings.width settings.headDim
  up layer :=
    frobeniusStretch (weights.perLayer.entry layer).shared.up settings.width
      (sharedHidden settings layer)
  scaledUp layer :=
    largestMagnitude tables.silu.entries
      * frobeniusStretch (weights.perLayer.entry layer).shared.up settings.width
        (sharedHidden settings layer)
  down layer :=
    frobeniusStretch (weights.perLayer.entry layer).shared.down (sharedHidden settings layer)
      settings.width
  routedUp layer expert :=
    frobeniusStretch ((weights.perLayer.entry layer).routed.entry expert).up settings.width
      settings.expertHidden
  routedScaledUp layer expert :=
    largestMagnitude tables.silu.entries
      * frobeniusStretch ((weights.perLayer.entry layer).routed.entry expert).up settings.width
        settings.expertHidden
  routedDown layer expert :=
    frobeniusStretch ((weights.perLayer.entry layer).routed.entry expert).down
      settings.expertHidden settings.width

/-- The Frobenius numbers hold, at all weights and for every list of taus. -/
theorem frobeniusLeastBoundNumbers_hold (s : Settings) (tables : Tables) (weights : Weights)
    (taus : List Int) :
    (frobeniusLeastBoundNumbers s tables weights taus).Hold s tables weights :=
  fun _ _ => ⟨stretchBound_frobenius _ _ _, fun _ _ => stretchBoundOf_frobenius _ _ _,
    ⟨stretchBound_frobenius _ _ _,
      stretch_scaled_columns _ _ _ _ _ _ _ _ (stretchBound_frobenius _ _ _),
      stretchBound_frobenius _ _ _⟩,
    fun _ _ _ => ⟨stretchBound_frobenius _ _ _,
      stretch_scaled_columns _ _ _ _ _ _ _ _ (stretchBound_frobenius _ _ _),
      stretchBound_frobenius _ _ _⟩⟩

/-- The same with the Frobenius numbers: every hypothesis is the value of a Boolean function. -/
theorem allConditionsHold_of_frobeniusLeastBoundCheck (s : Settings) (tables : Tables)
    (weights : Weights) (taus : List Int) (formed : wellFormed s tables weights = true)
    (passes : leastBoundWorstCaseCheck s tables weights
      (frobeniusLeastBoundNumbers s tables weights taus) = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) :
    allConditionsHold s (trace s tables weights prompt) = true :=
  allConditionsHold_of_leastBoundWorstCaseCheck s tables weights _ formed
    (frobeniusLeastBoundNumbers_hold s tables weights taus) passes prompt prompt_ok

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.allConditionsHold_of_leastBoundWorstCaseCheck
#print axioms IntegerTransformer.Bounds.allConditionsHold_of_frobeniusLeastBoundCheck
#print axioms IntegerTransformer.Bounds.frobeniusLeastBoundNumbers_hold
