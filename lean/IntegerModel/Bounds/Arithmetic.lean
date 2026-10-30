-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Bounds.Check
import IntegerModel.Readable.Facts
import IntegerModel.Readable.Reads

/-!
# Arithmetic of bounds

Small facts on absolute values, on `sumOver`, `roundShift`, `integerSquareRoot`, `clamp` and `product`, and on
the tools of IntegerModel/Bounds/Check.lean (`magnitude`, `allBelow`, `largestMagnitude`,
`columnBound`). They are proved from the specifications in IntegerModel/Readable/Facts.lean. Two of
them carry the rest: the triangle inequality for a sum of products (`magnitude_product_entry_le`),
and `magnitude_roundShift_le`: a bound on a sum gives a bound on the shifted sum.

Only Lean's core library is used. Nothing here speaks of the model as a whole.
-/

namespace IntegerTransformer.Bounds

/-- `|a| ≤ b` says that `a` is in `-b .. b`. -/
theorem magnitude_le_iff (a b : Int) : magnitude a ≤ b ↔ -b ≤ a ∧ a ≤ b := by
  unfold magnitude; omega

/-- An absolute value is not negative. -/
theorem magnitude_nonneg (a : Int) : 0 ≤ magnitude a := by
  unfold magnitude; omega

/-- The absolute value of a product is the product of the absolute values. -/
theorem magnitude_mul (a b : Int) : magnitude (a * b) = magnitude a * magnitude b := by
  unfold magnitude; rw [Int.natAbs_mul]; simp

/-- If `|a| ≤ b`, then `|a u| ≤ b |u|`. -/
theorem magnitude_mul_le (a u b : Int) (h : magnitude a ≤ b) :
    magnitude (a * u) ≤ b * magnitude u := by
  rw [magnitude_mul]
  exact Int.mul_le_mul_of_nonneg_right h (magnitude_nonneg u)

/-- The triangle inequality. -/
theorem magnitude_add_le (a b : Int) : magnitude (a + b) ≤ magnitude a + magnitude b := by
  unfold magnitude; omega

/-- The triangle inequality for `sumOver`: if `|f k| ≤ g k` for every `k < n`, the sum of the `f k`
is at most the sum of the `g k` in absolute value. -/
theorem magnitude_sumOver_le (n : Nat) (f g : Nat → Int)
    (h : ∀ k, k < n → magnitude (f k) ≤ g k) : magnitude (sumOver n f) ≤ sumOver n g := by
  induction n with
  | zero => simp [sumOver, magnitude]
  | succ n ih =>
    simp only [sumOver]
    have h1 := ih (fun k hk => h k (by omega))
    have h2 := h n (by omega)
    have h3 := magnitude_add_le (sumOver n f) (f n)
    omega

/-- `sumOver` does not fall when its terms grow. -/
theorem sumOver_le_sumOver (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k ≤ g k) :
    sumOver n f ≤ sumOver n g := by
  induction n with
  | zero => exact Int.le_refl _
  | succ n ih =>
    simp only [sumOver]
    have h1 := ih (fun k hk => h k (by omega))
    have h2 := h n (by omega)
    omega

/-- `2^k ≤ 2 * 2^(k - 1)`, also at `k = 0`, where `k - 1` is 0. -/
theorem two_mul_half_power (k : Nat) : (2 : Int) ^ k ≤ 2 * 2 ^ (k - 1) := by
  cases k with
  | zero => decide
  | succ k => simp [Int.pow_succ]; omega

/-- `roundShift` does not fall when its first argument grows. -/
theorem roundShift_le_roundShift (a b : Int) (k : Nat) (h : a ≤ b) :
    roundShift a k ≤ roundShift b k := by
  unfold roundShift
  exact Int.ediv_le_ediv (Int.pow_pos (by decide)) (by omega)

/-- If `|a| ≤ b`, then `|roundShift a k| ≤ roundShift b k`, for every shift `k`. -/
theorem magnitude_roundShift_le (a b : Int) (k : Nat) (h : magnitude a ≤ b) :
    magnitude (roundShift a k) ≤ roundShift b k := by
  rw [magnitude_le_iff] at h ⊢
  refine ⟨?_, roundShift_le_roundShift a b k h.2⟩
  have low := roundShift_le_roundShift (-b) a k h.1
  have specB := roundShift_spec b k
  have specN := roundShift_spec (-b) k
  have half := two_mul_half_power k
  have pos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  generalize roundShift b k = R at specB ⊢
  generalize roundShift (-b) k = r at specN low
  generalize (2 : Int) ^ k = m at *
  generalize (2 : Int) ^ (k - 1) = e at *
  apply Int.le_trans _ low
  apply Int.le_of_not_gt
  intro bad
  have step : (r + 1) * m ≤ (-R) * m := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  rw [Int.neg_mul] at step
  have expand : (R + 1) * m = R * m + m := by rw [Int.add_mul, Int.one_mul]
  omega

/-- `integerSquareRoot` does not fall when its argument grows. -/
theorem isqrt_le_isqrt (a b : Nat) (h : a ≤ b) : integerSquareRoot a ≤ integerSquareRoot b := by
  apply Nat.le_of_not_gt
  intro bad
  have sa := (isqrt_spec a).1
  have sb := (isqrt_spec b).2
  have : (integerSquareRoot b + 1) * (integerSquareRoot b + 1) ≤ integerSquareRoot a * integerSquareRoot a := Nat.mul_le_mul bad bad
  omega

/-- What `allBelow` says. -/
theorem allBelow_spec (n : Nat) (test : Nat → Bool) :
    allBelow n test = true ↔ ∀ k, k < n → test k = true := by
  simp [allBelow, List.all_eq_true]

/-- Every read of a vector, inside or outside, is at most `largestMagnitude` in absolute value. -/
theorem magnitude_entry_le_largestMagnitude (v : IntegerVector) (k : Nat) :
    magnitude (v.entry k) ≤ largestMagnitude v := by
  unfold largestMagnitude
  by_cases inside : k ≤ v.size
  · exact (maxUpTo_spec (fun k => magnitude (v.entry k)) v.size).1 k inside
  · rw [entry_outside v k (by omega)]
    have := (maxUpTo_spec (fun k => magnitude (v.entry k)) v.size).1 0 (by omega)
    have := magnitude_nonneg (v.entry 0)
    show magnitude 0 ≤ _
    simp only [magnitude] at *
    omega

/-- Every read of a keyed table, at any key, is at most the largest absolute value of its entries.
-/
theorem magnitude_read_le (table : KeyedTable) (key : Int) :
    magnitude (table.read key) ≤ largestMagnitude table.entries := by
  unfold KeyedTable.read
  split
  · exact magnitude_entry_le_largestMagnitude _ _
  · have := magnitude_entry_le_largestMagnitude table.entries 0
    have := magnitude_nonneg (table.entries.entry 0)
    simp only [magnitude] at *
    omega

/-- A vector whose entries are at most `b ≤ 32,767` in absolute value fits 16 bits. -/
theorem fits16_of_bounded (v : IntegerVector) (b : Int) (h : ∀ k, k < v.size → magnitude (v.entry k) ≤ b)
    (fits : b ≤ 32767) : fits16 v = true := by
  simp only [fits16, Array.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  intro k inside
  have := h k inside
  rw [entry_inside v k inside, magnitude_le_iff] at this
  omega

/-- Entry `j` of `product x W outputs` is at most `columnBound inputBound W x.size j` in absolute
value, if `|x[k]| ≤ inputBound k`. -/
theorem magnitude_product_entry_le (x : IntegerVector) (W : Matrix) (outputs j : Nat) (inside : j < outputs)
    (inputBound : Nat → Int) (h : ∀ k, k < x.size → magnitude (x.entry k) ≤ inputBound k) :
    magnitude ((product x W outputs).entry j) ≤ columnBound inputBound W x.size j := by
  unfold product columnBound
  rw [tabulate_read _ _ _ inside]
  exact magnitude_sumOver_le _ _ _ fun k hk => magnitude_mul_le _ _ _ (h k hk)

/-- If `|a| ≤ b`, then `a^2 ≤ b^2`. -/
theorem square_le_square (a b : Int) (h : magnitude a ≤ b) : a * a ≤ b * b := by
  have e : a * a = magnitude a * magnitude a := by
    rw [← magnitude_mul]; unfold magnitude; have := square_nonneg a; omega
  rw [e]
  exact Int.mul_le_mul h h (magnitude_nonneg a) (Int.le_trans (magnitude_nonneg a) h)

/-- For `b ≥ 0`, a clamped number is at most `b` in absolute value. -/
theorem magnitude_clamp_le (a b : Int) (h : 0 ≤ b) : magnitude (clamp a b) ≤ b := by
  rw [magnitude_le_iff]; unfold clamp; omega

end IntegerTransformer.Bounds
