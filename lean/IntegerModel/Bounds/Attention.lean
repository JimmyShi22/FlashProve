-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Bounds.FeedForward

/-!
# Bounds in attention

For a stream of at most `T` rows of `d` entries:
- `attention_out_within`: if every row is within a bound, every row after attention is within that
  bound plus `attentionAdditionBound`. No part of the check is used: a head's result is a mean of
  clamped values with weights that are not negative, rounded to the nearest, so it is in the box.
- `attentionOk_of_fits`: if also `normFits` and `attentionFits` pass, range conditions 1 to 4 hold
  at every position.

Of the softmax's table the proofs use what `wellFormed` tests: it is not empty, its first entry is
positive and no entry is negative. Of the scores they use nothing. Only Lean's core library is used.
-/

namespace IntegerTransformer.Bounds

/-- If `|a| ≤ b`, then `|c a| ≤ |c| b`. -/
theorem magnitude_mul_le_left (c a b : Int) (h : magnitude a ≤ b) :
    magnitude (c * a) ≤ magnitude c * b := by
  rw [magnitude_mul]
  exact Int.mul_le_mul_of_nonneg_left h (magnitude_nonneg c)

/-- The triangle inequality for a difference. -/
theorem magnitude_sub_le (a b : Int) : magnitude (a - b) ≤ magnitude a + magnitude b := by
  unfold magnitude; omega

/-- `boxColumnBound` is not negative. -/
theorem boxColumnBound_nonneg (W : Matrix) (rows column : Nat) :
    0 ≤ boxColumnBound W rows column := by
  unfold boxColumnBound columnBound
  exact sumOver_nonneg _ (fun k => Int.mul_nonneg (by decide) (magnitude_nonneg _)) _

/-- Every read of a product with an input in the box, inside or outside. -/
theorem product_read_le (a : IntegerVector) (W : Matrix) (outputs width : Nat) (size : a.size = width)
    (box : InBox a) (j : Nat) :
    magnitude ((product a W outputs).entry j) ≤ boxColumnBound W width j := by
  by_cases inside : j < outputs
  · have := magnitude_product_entry_le a W outputs j inside (fun _ => activationBound)
      (fun k _ => box k)
    rw [size] at this
    exact this
  · rw [entry_outside _ j (by rw [size_product]; exact inside)]
    exact boxColumnBound_nonneg W width j

/-- Entry `j` of a rotated vector is at most `rotatedBound` in absolute value. -/
theorem magnitude_rotate_entry_le (cosine sine : IntegerVector) (headDim : Nat) (A : IntegerVector)
    (productBound : Nat → Int) (h : ∀ j, magnitude (A.entry j) ≤ productBound j) (j : Nat)
    (inside : j < A.size) :
    magnitude ((rotate cosine sine headDim A).entry j) ≤
      rotatedBound cosine sine headDim productBound j := by
  unfold rotate rotatedBound
  rw [tabulate_read _ _ _ inside]
  dsimp only
  split
  · have h1 := magnitude_mul_le_left (cosine.entry (j % headDim / 2)) _ _ (h j)
    have h2 := magnitude_mul_le_left (sine.entry (j % headDim / 2)) _ _ (h (j + 1))
    have h3 := magnitude_sub_le (cosine.entry (j % headDim / 2) * A.entry j)
      (sine.entry (j % headDim / 2) * A.entry (j + 1))
    omega
  · have h1 := magnitude_mul_le_left (sine.entry (j % headDim / 2)) _ _ (h (j - 1))
    have h2 := magnitude_mul_le_left (cosine.entry (j % headDim / 2)) _ _ (h j)
    have h3 := magnitude_add_le (sine.entry (j % headDim / 2) * A.entry (j - 1))
      (cosine.entry (j % headDim / 2) * A.entry j)
    omega

/-- A rotated and shifted product fits 16 bits, if its bounds do. -/
theorem rotated_fits (cosine sine : IntegerVector) (headDim : Nat) (a : IntegerVector) (W : Matrix)
    (outputs width shift : Nat) (size : a.size = width) (box : InBox a)
    (fits : ∀ j, j < outputs →
      roundShift (rotatedBound cosine sine headDim (boxColumnBound W width) j) shift ≤ 32767) :
    fits16 ((rotate cosine sine headDim (product a W outputs)).map fun e => roundShift e shift) =
      true := by
  apply fits16_of_bounded _ 32767 _ (Int.le_refl _)
  intro j inside
  rw [Array.size_map, size_rotate, size_product] at inside
  rw [map_read _ _ _ (by rw [size_rotate, size_product]; exact inside)]
  apply Int.le_trans _ (fits j inside)
  apply magnitude_roundShift_le
  exact magnitude_rotate_entry_le cosine sine headDim _ _
    (product_read_le a W outputs width size box) j (by rw [size_product]; exact inside)

/-- Conditions 3 and 4 hold at a position below `T` for a normed row in the box, if `attentionFits`
passes. -/
theorem projections_fit (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (t : Nat) (a : IntegerVector) (position : t < s.positions) (size : a.size = s.width) (box : InBox a)
    (fits : attentionFits s p tables w = true) :
    fits16 (projections s p tables w t a).wideQuery = true ∧
    fits16 (projections s p tables w t a).wideKey = true ∧
    fits16 (projections s p tables w t a).wideValue = true := by
  simp only [attentionFits, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq] at fits
  refine ⟨?_, ?_, ?_⟩
  · exact rotated_fits (cosineRow s p tables t) (sineRow s p tables t) s.headDim a w.query
      s.queryWidth s.width p.queryShift size box (fits.1 t position).1
  · exact rotated_fits (cosineRow s p tables t) (sineRow s p tables t) s.headDim a w.key
      s.keyValueWidth s.width p.keyShift size box (fits.1 t position).2
  · apply fits16_of_bounded _ 32767 _ (Int.le_refl _)
    intro j inside
    rw [(size_projections s p tables w t a).2.2.1] at inside
    exact Int.le_trans
      (shifted_product_le a w.value s.keyValueWidth p.valueShift s.width j size box inside)
      (fits.2 j inside)

/-- The values of a position are in the box: they are clamped. -/
theorem projections_value_inBox (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (t : Nat) (a : IntegerVector) : InBox (projections s p tables w t a).value :=
  map_clamp_inBox _

/-- A common factor can be taken out of `sumOver`. -/
theorem sumOver_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumOver n (fun k => f k * c) = sumOver n f * c := by
  induction n with
  | zero => simp [sumOver]
  | succ n ih => simp only [sumOver, ih, Int.add_mul]

/-- A mean with weights that are not negative, rounded to the nearest, stays within the bound of
what is averaged. -/
theorem rounded_mean_le (acc total b : Int) (positive : 0 < total)
    (h : magnitude acc ≤ total * b) : magnitude ((2 * acc + total) / (2 * total)) ≤ b := by
  rw [magnitude_le_iff] at h ⊢
  constructor
  · apply (Int.le_ediv_iff_mul_le (by omega)).mpr
    have e : -b * (2 * total) = -(2 * (total * b)) := by grind
    omega
  · apply Int.lt_add_one_iff.mp
    apply (Int.ediv_lt_iff_lt_mul (by omega)).mpr
    have e : (b + 1) * (2 * total) = 2 * (total * b) + 2 * total := by grind
    omega

/-- No weight of the softmax is negative, if no entry of its table is. -/
theorem exponentials_nonneg (s : Settings) (p : LayerSettings) (tables : Tables)
    (projected : Array Projections) (i h : Nat)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true) (j : Nat) :
    0 ≤ (attendHead s p tables projected i h).exponentials.entry j := by
  have made : (attendHead s p tables projected i h).exponentials =
      (attendHead s p tables projected i h).distances.map fun (u : Int) =>
        if u < tables.exponential.size then tables.exponential.entry u.toNat else 0 := rfl
  by_cases inside : j < (attendHead s p tables projected i h).distances.size
  · rw [made, map_read _ _ _ inside]
    split
    · exact read_nonneg _ none_negative _
    · exact Int.le_refl 0
  · rw [entry_outside _ j (by rw [made, Array.size_map]; exact inside)]
    exact Int.le_refl 0

/-- A head's result is in the box, if the values that it reads are. -/
theorem attendHead_out_inBox (s : Settings) (p : LayerSettings) (tables : Tables)
    (projected : Array Projections) (i h : Nat)
    (values : ∀ j, j < i + 1 → InBox (projected.entry j).value)
    (some_entry : 0 < tables.exponential.size) (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true) :
    InBox (attendHead s p tables projected i h).out := by
  intro c
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
  by_cases inside : c < s.headDim
  · rw [made, map_read _ _ _ (by rw [size]; exact inside)]
    apply rounded_mean_le _ _ _ positive
    rw [mixed, tabulate_read _ _ _ inside, total, ← sumOver_mul_right]
    apply magnitude_sumOver_le
    intro j hj
    apply magnitude_mul_le_mul
    · have := nonneg j
      unfold magnitude; omega
    · exact values j hj _
  · rw [entry_outside _ c (by rw [made, Array.size_map, size]; exact inside)]; decide

/-- The heads' results side by side are in the box, at every position. -/
theorem attention_mixed_inBox (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix)
    (some_entry : 0 < tables.exponential.size) (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true)
    (t : Nat) (ht : t < x.size) : InBox ((attention s p tables w x).mixed.entry t) := by
  intro j
  have size := (size_attention_rows s p tables w x t ht).2.1
  by_cases inside : j < s.queryWidth
  · have split := split_index s.queryHeads s.headDim j inside
    have made : ((attention s p tables w x).mixed.entry t).entry j =
        (attendHead s p tables (attention s p tables w x).projected t (j / s.headDim)).out.entry
          (j % s.headDim) := by
      simp only [attention, tabulate_read, ht, inside, split.1]
    rw [made]
    apply attendHead_out_inBox s p tables _ t _ _ some_entry first none_negative
    intro i hi
    have read : (attention s p tables w x).projected.entry i =
        projections s p tables w i ((attention s p tables w x).norm.entry i).out := by
      simp only [attention, tabulate_read, (by omega : i < x.size)]
    rw [read]
    exact projections_value_inBox _ _ _ _ _ _
  · rw [entry_outside _ j (by rw [size]; exact inside)]; decide

/-- The stream after attention. No part of the check is used. -/
theorem attention_out_within (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix) (bound : Nat → Int)
    (some_entry : 0 < tables.exponential.size) (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true)
    (rows : ∀ t, t < x.size → (x.entry t).size = s.width)
    (within : ∀ t, t < x.size → RowWithin bound (x.entry t)) (t : Nat) (ht : t < x.size) :
    RowWithin (fun k => bound k + attentionAdditionBound s p w k)
      ((attention s p tables w x).out.entry t) := by
  have box := attention_mixed_inBox s p tables w x some_entry first none_negative t ht
  have size := (size_attention_rows s p tables w x t ht).2.1
  have made : (attention s p tables w x).out.entry t =
      addVectors (x.entry t) (((product ((attention s p tables w x).mixed.entry t) w.output
            s.width).map fun e => roundShift e p.outputShift)) := by
    simp only [attention, tabulate_read, map_read, size_tabulate, ht]
  rw [made]
  apply addVec_within _ _ bound _ (within t ht)
  intro k inside
  exact shifted_product_le _ w.output s.width p.outputShift s.queryWidth k size box
    (by rw [← rows t ht]; exact inside)

/-- Conditions 1 to 4 at one position of one layer. -/
theorem attentionOk_of_fits (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix) (bound : Nat → Int) (eps_pos : 1 ≤ p.attentionEps)
    (few : x.size ≤ s.positions) (rows : ∀ t, t < x.size → (x.entry t).size = s.width)
    (within : ∀ t, t < x.size → RowWithin bound (x.entry t))
    (normFit : normFits p.attentionBits p.attentionShift p.attentionEps s.width bound = true)
    (fits : attentionFits s p tables w = true) (t : Nat) (ht : t < x.size) :
    attentionOk p (attention s p tables w x) t = true := by
  have norm : (attention s p tables w x).norm.entry t =
      rmsNorm p.attentionBits p.attentionShift p.attentionEps (x.entry t) := by
    simp only [attention, map_read, ht]
  have read : (attention s p tables w x).projected.entry t =
      projections s p tables w t ((attention s p tables w x).norm.entry t).out := by
    simp only [attention, tabulate_read, ht]
  have parts := projections_fit s p tables w t
    (rmsNorm p.attentionBits p.attentionShift p.attentionEps (x.entry t)).out (by omega)
    (by rw [(size_rmsNorm _ _ _ _).2, rows t ht]) (norm_out_inBox _ _ _ _) fits
  simp only [attentionOk, Bool.and_eq_true]
  rw [read, norm]
  have normed := normOk_of_normFits _ _ _ _ bound eps_pos (within t ht)
    (by rw [rows t ht]; exact normFit)
  exact ⟨⟨⟨normed, parts.1⟩, parts.2.1⟩, parts.2.2⟩

end IntegerTransformer.Bounds
