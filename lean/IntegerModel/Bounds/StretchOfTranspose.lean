-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/StretchOfTranspose.lean

A matrix and its transpose stretch alike, so the tests of IntegerModel/Bounds/GramIteration.lean and
IntegerModel/Bounds/ScaledGramIteration.lean may be made on either side of a matrix.
- `stretchBoundOf_of_transpose`: if `StretchBoundOf` holds of the transposed entries with the number
  `stretch`, it holds of the entries with the same number.
- `stretchBoundOf_of_gramIterationFitsOf_transpose`,
  `stretchBoundOf_of_scaledGramIterationFitsOf_transpose`: so a test that says yes at the transposed
  entries gives `StretchBoundOf` of the entries.
- `gramIterationFitsOnSmallerSideOf`, `scaledGramIterationFitsOnSmallerSideOf`: the tests at the
  transposed entries if there are fewer columns than rows, and at the entries if not; with
  `stretchBoundOf_of_gramIterationFitsOnSmallerSideOf` and
  `stretchBoundOf_of_scaledGramIterationFitsOnSmallerSideOf`.
What it buys: the tests work on a square matrix with as many rows as the matrix that is tested. At
the transposed entries that number is the number of columns.
The proof uses the inequality of Cauchy and Schwarz and the exchange of two sums: for `y`, the row
`v` times the matrix, the squared length of `y` is the inner product of `v` with `y` times the
transpose.
Limits: those at the heads of the two files. The levels of the scaled test belong to the side on
which the test is made. The file says of no matrix of a model that it passes. It imports Lean's core
and the model's own files.
-/
import IntegerModel.Bounds.ScaledGramIteration

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-! ## 1. Sums -/

/-- A sum of zeros is zero. -/
private theorem sumOver_zeros (n : Nat) : sumOver n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n step => simp only [sumOver]; rw [step]; rfl

/-- A factor on the left can be taken out of a sum. -/
private theorem sumOver_left_factor (n : Nat) (c : Int) (f : Nat → Int) :
    sumOver n (fun k => c * f k) = c * sumOver n f := by
  induction n with
  | zero => simp only [sumOver, Int.mul_zero]
  | succ n step => simp only [sumOver]; rw [step, Int.mul_add]

/-- A factor on the right can be taken out of a sum. -/
private theorem sumOver_right_factor (n : Nat) (f : Nat → Int) (c : Int) :
    sumOver n (fun k => f k * c) = sumOver n f * c := by
  induction n with
  | zero => simp only [sumOver, Int.zero_mul]
  | succ n step => simp only [sumOver]; rw [step, Int.add_mul]

/-- The sum of sums, term by term. -/
private theorem sumOver_of_sums (n : Nat) (f g : Nat → Int) :
    sumOver n (fun k => f k + g k) = sumOver n f + sumOver n g := by
  induction n with
  | zero => rfl
  | succ n step => simp only [sumOver]; rw [step]; omega

/-- Two sums can be exchanged. -/
private theorem sumOver_exchanged (m n : Nat) (f : Nat → Nat → Int) :
    sumOver m (fun a => sumOver n fun b => f a b) =
      sumOver n fun b => sumOver m fun a => f a b := by
  induction m with
  | zero => simp only [sumOver]; rw [sumOver_zeros]
  | succ m step => simp only [sumOver]; rw [sumOver_of_sums, step]

/-- The inner product of `y` with `v` times the matrix is that of `y` times the transpose with
`v`. -/
private theorem inner_product_exchanged (entries : Nat → Nat → Int) (rows columns : Nat)
    (v y : Nat → Int) :
    sumOver columns (fun column => y column * sumOver rows fun row => v row * entries row column) =
      sumOver rows fun row => (sumOver columns fun column => y column * entries row column) *
        v row := by
  have left : (fun column => y column * sumOver rows fun row => v row * entries row column) =
      fun column => sumOver rows fun row => y column * entries row column * v row := by
    funext column
    rw [← sumOver_left_factor]
    exact congrArg (sumOver rows) (funext fun row => by
      rw [Int.mul_comm (v row), Int.mul_assoc])
  have right : (fun row => (sumOver columns fun column => y column * entries row column) * v row) =
      fun row => sumOver columns fun column => y column * entries row column * v row :=
    funext fun row =>
      (sumOver_right_factor columns (fun column => y column * entries row column) (v row)).symm
  rw [left, right, sumOver_exchanged]

/-! ## 2. The transpose -/

/-- **A bound on the stretch of the transposed entries is a bound on the stretch of the
entries.** -/
theorem stretchBoundOf_of_transpose (entries : Nat → Nat → Int) (rows columns : Nat)
    (stretch : Int)
    (transposed : StretchBoundOf (fun column row => entries row column) columns rows stretch) :
    StretchBoundOf entries rows columns stretch := by
  refine ⟨transposed.1, fun v => ?_⟩
  have back := transposed.2 fun column => sumOver rows fun row => v row * entries row column
  have inner := inner_product_exchanged entries rows columns v
    fun column => sumOver rows fun row => v row * entries row column
  have schwarz := cauchy_schwarz rows
    (fun row => sumOver columns fun column =>
      (sumOver rows fun row => v row * entries row column) * entries row column) v
  rw [← inner] at schwarz
  have lengthNonneg := sumSquaresOver_nonneg rows v
  have imageNonneg := sumSquaresOver_nonneg columns
    fun column => sumOver rows fun row => v row * entries row column
  have scaled := Int.mul_le_mul_of_nonneg_right back lengthNonneg
  have image : sumOver columns (fun column =>
      (sumOver rows fun row => v row * entries row column) *
        sumOver rows fun row => v row * entries row column) =
      sumSquaresOver columns fun column => sumOver rows fun row => v row * entries row column :=
    rfl
  rw [image] at schwarz
  generalize sumSquaresOver columns
    (fun column => sumOver rows fun row => v row * entries row column) = squaredImage at *
  generalize sumSquaresOver rows v = squaredLength at *
  by_cases none : squaredImage = 0
  · rw [none]
    exact Int.mul_nonneg (square_nonneg stretch) lengthNonneg
  · apply Int.le_of_mul_le_mul_left _ (by omega : 0 < squaredImage)
    have same : stretch * stretch * squaredImage * squaredLength =
        squaredImage * (stretch * stretch * squaredLength) := by grind
    exact Int.le_trans schwarz (Int.le_trans scaled (Int.le_of_eq same))

/-- The exact test at the transposed entries. -/
theorem stretchBoundOf_of_gramIterationFitsOf_transpose (entries : Nat → Nat → Int)
    (rows columns steps : Nat) (stretch : Int)
    (fits : gramIterationFitsOf (fun column row => entries row column) columns rows steps stretch =
      true) : StretchBoundOf entries rows columns stretch :=
  stretchBoundOf_of_transpose entries rows columns stretch
    (stretchBoundOf_of_gramIterationFitsOf _ columns rows steps stretch fits)

/-- The scaled test at the transposed entries. -/
theorem stretchBoundOf_of_scaledGramIterationFitsOf_transpose (entries : Nat → Nat → Int)
    (rows columns : Nat) (levels : List ScaledLevel) (stretch : Int)
    (fits : scaledGramIterationFitsOf (fun column row => entries row column) columns rows levels
      stretch = true) : StretchBoundOf entries rows columns stretch :=
  stretchBoundOf_of_transpose entries rows columns stretch
    (stretchBoundOf_of_scaledGramIterationFitsOf _ columns rows levels stretch fits)

/-! ## 3. The tests on the smaller side -/

/-- The exact test, at the transposed entries if there are fewer columns than rows. -/
def gramIterationFitsOnSmallerSideOf (entries : Nat → Nat → Int) (rows columns steps : Nat)
    (stretch : Int) : Bool :=
  if columns < rows then
    gramIterationFitsOf (fun column row => entries row column) columns rows steps stretch
  else gramIterationFitsOf entries rows columns steps stretch

/-- The scaled test, at the transposed entries if there are fewer columns than rows. The levels are
those of the side on which the test is made. -/
def scaledGramIterationFitsOnSmallerSideOf (entries : Nat → Nat → Int) (rows columns : Nat)
    (levels : List ScaledLevel) (stretch : Int) : Bool :=
  if columns < rows then
    scaledGramIterationFitsOf (fun column row => entries row column) columns rows levels stretch
  else scaledGramIterationFitsOf entries rows columns levels stretch

/-- **A matrix that passes the exact test on its smaller side stretches no vector by more than
`stretch`.** -/
theorem stretchBoundOf_of_gramIterationFitsOnSmallerSideOf (entries : Nat → Nat → Int)
    (rows columns steps : Nat) (stretch : Int)
    (fits : gramIterationFitsOnSmallerSideOf entries rows columns steps stretch = true) :
    StretchBoundOf entries rows columns stretch := by
  unfold gramIterationFitsOnSmallerSideOf at fits
  split at fits
  · exact stretchBoundOf_of_gramIterationFitsOf_transpose entries rows columns steps stretch fits
  · exact stretchBoundOf_of_gramIterationFitsOf entries rows columns steps stretch fits

/-- **A matrix that passes the scaled test on its smaller side stretches no vector by more than
`stretch`.** -/
theorem stretchBoundOf_of_scaledGramIterationFitsOnSmallerSideOf (entries : Nat → Nat → Int)
    (rows columns : Nat) (levels : List ScaledLevel) (stretch : Int)
    (fits : scaledGramIterationFitsOnSmallerSideOf entries rows columns levels stretch = true) :
    StretchBoundOf entries rows columns stretch := by
  unfold scaledGramIterationFitsOnSmallerSideOf at fits
  split at fits
  · exact stretchBoundOf_of_scaledGramIterationFitsOf_transpose entries rows columns levels stretch
      fits
  · exact stretchBoundOf_of_scaledGramIterationFitsOf entries rows columns levels stretch fits

/-! ## 4. The tests on a small matrix

The matrix with the three rows (2), (3), (6), of one column, stretches by 7. On its smaller side the
tests work on the one number 49: 7 passes and 6 does not, in both tests. A level for that side: 49
is 7 times 7, with no error, and the bound is 7. -/

/-- The entries of the matrix with the rows (2), (3), (6). -/
private def threeRowsOneColumn : Nat → Nat → Int :=
  fun row _ => if row = 0 then 2 else if row = 1 then 3 else 6

example : gramIterationFitsOnSmallerSideOf threeRowsOneColumn 3 1 0 7 = true := by decide
example : gramIterationFitsOnSmallerSideOf threeRowsOneColumn 3 1 0 6 = false := by decide
example : gramIterationFitsOnSmallerSideOf threeRowsOneColumn 3 1 2 7 = true := by decide
example : scaledGramIterationFitsOnSmallerSideOf threeRowsOneColumn 3 1 [] 7 = true := by decide
example : scaledGramIterationFitsOnSmallerSideOf threeRowsOneColumn 3 1
    [⟨fun _ _ => 7, 7, 0, 7⟩] 7 = true := by decide
example : scaledGramIterationFitsOnSmallerSideOf threeRowsOneColumn 3 1
    [⟨fun _ _ => 7, 7, 0, 7⟩] 6 = false := by decide

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.stretchBoundOf_of_transpose
#print axioms IntegerTransformer.Bounds.stretchBoundOf_of_gramIterationFitsOnSmallerSideOf
#print axioms IntegerTransformer.Bounds.stretchBoundOf_of_scaledGramIterationFitsOnSmallerSideOf
