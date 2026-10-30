-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/GramIteration.lean

A test in whole numbers that bounds how much a matrix can stretch a vector, and its proof.
- `gramIterationFitsOf entries rows columns steps stretch`, for the matrix with the entry
  `entries row column`: form the matrix times its transpose (`gramMatrixOf`), square that `steps`
  times (`gramPowerOf`), and ask that the sum of the squares of the entries be at most
  `(stretch * stretch) ^ (2 ^ (steps + 1))`, with `0 ≤ stretch`.
- `StretchBoundOf entries rows columns stretch`: `0 ≤ stretch`, and no vector of whole numbers gets
  longer by more than the factor `stretch` when it is multiplied with the matrix.
- `stretchBoundOf_of_gramIterationFitsOf`: if the test says yes, then `StretchBoundOf` holds.
- `gramIterationFits matrix rows columns steps stretch`: the test for the entries of an array of
  rows.
The entries are a function, so the test also serves a slice of a matrix and a matrix with scaled
rows or columns.
The proof uses the inequality of Cauchy and Schwarz, the exchange of two sums and an induction on
the number of squarings; it uses no eigenvalue and no root. At `steps = 0` the test compares with
the sum of the squares of the entries of the matrix times its transpose.
Limits: the test rounds nothing: it computes with the whole numbers as they are; that is what "the
exact test" means in this folder. It is costly to evaluate. The definitions are written to be proved
over: the matrices are functions and nothing is stored, so, evaluated as they stand, they compute an
entry anew at each read, and each squaring multiplies the cost by about twice the number of rows. An
evaluator that stores each matrix needs about `rows ^ 3` products for a squaring. The entries have
about twice as many digits after each squaring. The theorem goes one way: a `stretch` that fails the
test may still be a bound. How close the least `stretch` that passes comes to the largest singular
value is not stated here. The file says of no matrix of a model that it passes. It imports Lean's
core and the model's own files.
-/
import IntegerModel.Bounds.Lengths

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-! ## 1. Sums -/

/-- A sum of zeros is zero. -/
private theorem sumOver_zero (n : Nat) : sumOver n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n step => simp only [sumOver]; rw [step]; rfl

/-- A factor on the left can be taken out of a sum. -/
private theorem sumOver_factor_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumOver n (fun k => c * f k) = c * sumOver n f := by
  induction n with
  | zero => simp only [sumOver, Int.mul_zero]
  | succ n step => simp only [sumOver]; rw [step, Int.mul_add]

/-- A factor on the right can be taken out of a sum. -/
private theorem sumOver_factor_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumOver n (fun k => f k * c) = sumOver n f * c := by
  induction n with
  | zero => simp only [sumOver, Int.zero_mul]
  | succ n step => simp only [sumOver]; rw [step, Int.add_mul]

/-- The sum of sums, term by term. -/
private theorem sumOver_add (n : Nat) (f g : Nat → Int) :
    sumOver n (fun k => f k + g k) = sumOver n f + sumOver n g := by
  induction n with
  | zero => rfl
  | succ n step => simp only [sumOver]; rw [step]; omega

/-- Two sums can be exchanged. -/
private theorem sumOver_exchange (m n : Nat) (f : Nat → Nat → Int) :
    sumOver m (fun a => sumOver n fun b => f a b) =
      sumOver n fun b => sumOver m fun a => f a b := by
  induction m with
  | zero => simp only [sumOver]; rw [sumOver_zero]
  | succ m step => simp only [sumOver]; rw [sumOver_add, step]

/-- A row `x`, a matrix `M` and a column `y`: the product can be formed from either side. -/
private theorem bilinear_exchange (m n : Nat) (x : Nat → Int) (M : Nat → Nat → Int)
    (y : Nat → Int) :
    sumOver m (fun a => x a * sumOver n fun r => M a r * y r) =
      sumOver n fun r => (sumOver m fun a => x a * M a r) * y r := by
  have left : (fun a => x a * sumOver n fun r => M a r * y r) =
      fun a => sumOver n fun r => x a * M a r * y r := by
    funext a
    rw [← sumOver_factor_left]
    exact congrArg (sumOver n) (funext fun r => (Int.mul_assoc _ _ _).symm)
  have right : (fun r => (sumOver m fun a => x a * M a r) * y r) =
      fun r => sumOver m fun a => x a * M a r * y r :=
    funext fun r => (sumOver_factor_right m (fun a => x a * M a r) (y r)).symm
  rw [left, right, sumOver_exchange]

/-! ## 2. Square matrices as functions -/

/-- The product of the `size` by `size` matrix with itself. -/
def squareMatrix (size : Nat) (matrix : Nat → Nat → Int) : Nat → Nat → Int :=
  fun row column => sumOver size fun middle => matrix row middle * matrix middle column

/-- The matrix, squared `steps` times: its power `2 ^ steps`. -/
def repeatedSquare (size : Nat) (matrix : Nat → Nat → Int) : Nat → Nat → Nat → Int
  | 0 => matrix
  | steps + 1 => squareMatrix size (repeatedSquare size matrix steps)

/-- The sum of the squares of all entries of the `size` by `size` matrix. -/
def sumSquaresOfEntries (size : Nat) (matrix : Nat → Nat → Int) : Int :=
  sumOver size fun row => sumSquaresOver size (matrix row)

/-- The matrix times the column `vector`. -/
def applyMatrix (size : Nat) (matrix : Nat → Nat → Int) (vector : Nat → Int) : Nat → Int :=
  fun row => sumOver size fun column => matrix row column * vector column

/-- The row `vector` times the matrix times the column `vector`. -/
def quadraticForm (size : Nat) (matrix : Nat → Nat → Int) (vector : Nat → Int) : Int :=
  sumOver size fun row => vector row * applyMatrix size matrix vector row

/-- The square of a symmetric matrix is symmetric. -/
theorem squareMatrix_symmetric (size : Nat) (G : Nat → Nat → Int)
    (symmetric : ∀ row column, G row column = G column row) (row column : Nat) :
    squareMatrix size G row column = squareMatrix size G column row := by
  unfold squareMatrix
  refine congrArg (sumOver size) (funext fun k => ?_)
  rw [symmetric row k, symmetric k column, Int.mul_comm]

/-- One squaring more can be done first as well as last. -/
theorem repeatedSquare_succ (size : Nat) (G : Nat → Nat → Int) (steps : Nat) :
    repeatedSquare size G (steps + 1) = repeatedSquare size (squareMatrix size G) steps := by
  induction steps with
  | zero => rfl
  | succ steps step =>
    show squareMatrix size (repeatedSquare size G (steps + 1)) =
      squareMatrix size (repeatedSquare size (squareMatrix size G) steps)
    rw [step]

/-- The square of `G` times `v` is `G` times (`G` times `v`). -/
theorem applyMatrix_squareMatrix (size : Nat) (G : Nat → Nat → Int) (v : Nat → Int) :
    applyMatrix size (squareMatrix size G) v = applyMatrix size G (applyMatrix size G v) :=
  funext fun row => (bilinear_exchange size size (G row) G v).symm

/-- For a symmetric `G`, the squared length of `G` times `v` is the quadratic form of the square of
`G` at `v`. -/
theorem sumSquaresOver_applyMatrix (size : Nat) (G : Nat → Nat → Int)
    (symmetric : ∀ row column, G row column = G column row) (v : Nat → Int) :
    sumSquaresOver size (applyMatrix size G v) = quadraticForm size (squareMatrix size G) v := by
  unfold quadraticForm
  rw [applyMatrix_squareMatrix]
  have exchanged := bilinear_exchange size size v G (applyMatrix size G v)
  have sameRow : (fun r => (sumOver size fun a => v a * G a r) * applyMatrix size G v r) =
      fun r => applyMatrix size G v r * applyMatrix size G v r := by
    funext r
    have same : (fun a => v a * G a r) = fun a => G r a * v a :=
      funext fun a => by rw [symmetric a r, Int.mul_comm]
    rw [same]
    rfl
  rw [sameRow] at exchanged
  exact exchanged.symm

/-- Cauchy and Schwarz for the quadratic form: its square is at most the squared length of `v` times
the squared length of `G` times `v`. -/
theorem square_quadraticForm_le (size : Nat) (G : Nat → Nat → Int) (v : Nat → Int) :
    quadraticForm size G v * quadraticForm size G v ≤
      sumSquaresOver size v * sumSquaresOver size (applyMatrix size G v) :=
  cauchy_schwarz size v (applyMatrix size G v)

/-- Cauchy and Schwarz row by row: the squared length of `G` times `v` is at most the sum of the
squares of the entries of `G` times the squared length of `v`. -/
theorem sumSquaresOver_applyMatrix_le (size : Nat) (G : Nat → Nat → Int) (v : Nat → Int) :
    sumSquaresOver size (applyMatrix size G v) ≤
      sumSquaresOfEntries size G * sumSquaresOver size v := by
  unfold sumSquaresOfEntries
  rw [← sumOver_factor_right]
  exact sumOver_le_sumOver _ _ _ fun row _ => cauchy_schwarz size (G row) v

/-- The last step of both cases of the induction, on numbers alone. -/
private theorem le_of_square_le_of_le {form length middle bound : Int} (lengthNonneg : 0 ≤ length)
    (boundNonneg : 0 ≤ bound) (square : form * form ≤ length * middle)
    (small : middle ≤ bound * bound * length) : form ≤ bound * length := by
  apply le_of_square_le (Int.mul_nonneg boundNonneg lengthNonneg)
  have scaled := Int.mul_le_mul_of_nonneg_left small lengthNonneg
  have same : length * (bound * bound * length) = bound * length * (bound * length) := by grind
  omega

/-- **The iteration.** If `G` is symmetric and the sum of the squares of the entries of its power
`2 ^ steps` is at most `bound ^ (2 ^ (steps + 1))`, then the quadratic form of `G` at `v` is at most
`bound` times the squared length of `v`. -/
theorem quadraticForm_le_of_repeatedSquare (size : Nat) (v : Nat → Int) (steps : Nat) :
    ∀ (G : Nat → Nat → Int) (_ : ∀ row column, G row column = G column row) (bound : Int)
      (_ : 0 ≤ bound)
      (_ : sumSquaresOfEntries size (repeatedSquare size G steps) ≤ bound ^ (2 ^ (steps + 1))),
      quadraticForm size G v ≤ bound * sumSquaresOver size v := by
  have lengthNonneg := sumSquaresOver_nonneg size v
  induction steps with
  | zero =>
    intro G _ bound boundNonneg fits
    have power : bound ^ (2 ^ (0 + 1)) = bound * bound := by
      show bound ^ 2 = bound * bound
      rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
    rw [power] at fits
    exact le_of_square_le_of_le lengthNonneg boundNonneg (square_quadraticForm_le size G v)
      (Int.le_trans (sumSquaresOver_applyMatrix_le size G v)
        (Int.mul_le_mul_of_nonneg_right fits lengthNonneg))
  | succ steps step =>
    intro G symmetric bound boundNonneg fits
    have power : bound ^ (2 ^ (steps + 1 + 1)) = (bound * bound) ^ (2 ^ (steps + 1)) := by
      rw [Int.mul_pow, ← Int.pow_add]
      congr 1
      rw [Nat.pow_succ 2 (steps + 1)]
      omega
    rw [power, repeatedSquare_succ] at fits
    have squared := step (squareMatrix size G) (squareMatrix_symmetric size G symmetric)
      (bound * bound) (Int.mul_nonneg boundNonneg boundNonneg) fits
    have square := square_quadraticForm_le size G v
    rw [sumSquaresOver_applyMatrix size G symmetric v] at square
    exact le_of_square_le_of_le lengthNonneg boundNonneg square squared

/-! ## 3. The matrix with given entries -/

/-- `stretch` is at or above the largest singular value of the matrix with the entry
`entries row column`: no vector of whole numbers gets longer by more than this factor when it is
multiplied with the matrix. -/
def StretchBoundOf (entries : Nat → Nat → Int) (rows columns : Nat) (stretch : Int) : Prop :=
  0 ≤ stretch ∧ ∀ vector : Nat → Int,
    sumSquaresOver columns (fun column => sumOver rows fun row => vector row * entries row column)
      ≤ stretch * stretch * sumSquaresOver rows vector

/-- The matrix times its transpose: entry `(row, other)` is the inner product of these two rows,
over the first `columns` columns. -/
def gramMatrixOf (entries : Nat → Nat → Int) (columns : Nat) : Nat → Nat → Int :=
  fun row other => sumOver columns fun column => entries row column * entries other column

/-- The matrix times its transpose, squared `steps` times. -/
def gramPowerOf (entries : Nat → Nat → Int) (rows columns steps : Nat) : Nat → Nat → Int :=
  repeatedSquare rows (gramMatrixOf entries columns) steps

/-- **The Gram test.** Is `stretch` not negative, and is the sum of the squares of the entries of
the matrix times its transpose, squared `steps` times, at most
`(stretch * stretch) ^ (2 ^ (steps + 1))`? -/
def gramIterationFitsOf (entries : Nat → Nat → Int) (rows columns steps : Nat) (stretch : Int) :
    Bool :=
  decide (0 ≤ stretch) &&
    decide (sumSquaresOfEntries rows (gramPowerOf entries rows columns steps) ≤
      (stretch * stretch) ^ (2 ^ (steps + 1)))

/-- A matrix times its transpose is symmetric. -/
theorem gramMatrixOf_symmetric (entries : Nat → Nat → Int) (columns row other : Nat) :
    gramMatrixOf entries columns row other = gramMatrixOf entries columns other row :=
  congrArg (sumOver columns) (funext fun _ => Int.mul_comm _ _)

/-- The squared length of the row `v` times the matrix is the quadratic form of the matrix times its
transpose at `v`. -/
theorem sumSquaresOver_product (entries : Nat → Nat → Int) (rows columns : Nat) (v : Nat → Int) :
    sumSquaresOver columns (fun column => sumOver rows fun row => v row * entries row column) =
      quadraticForm rows (gramMatrixOf entries columns) v := by
  have applied : applyMatrix rows (gramMatrixOf entries columns) v = fun row =>
      sumOver columns fun column => entries row column *
        sumOver rows fun other => v other * entries other column := by
    funext row
    have exchanged := bilinear_exchange columns rows (fun column => entries row column)
      (fun column other => entries other column) v
    have turned : (fun column => entries row column *
        sumOver rows fun other => entries other column * v other) =
        fun column => entries row column *
          sumOver rows fun other => v other * entries other column :=
      funext fun column => congrArg _ (congrArg (sumOver rows) (funext fun _ => Int.mul_comm _ _))
    rw [turned] at exchanged
    exact exchanged.symm
  unfold quadraticForm
  rw [applied]
  exact (bilinear_exchange rows columns v entries
    (fun column => sumOver rows fun row => v row * entries row column)).symm

/-- **A matrix that passes the Gram test stretches no vector by more than `stretch`.** -/
theorem stretchBoundOf_of_gramIterationFitsOf (entries : Nat → Nat → Int)
    (rows columns steps : Nat) (stretch : Int)
    (fits : gramIterationFitsOf entries rows columns steps stretch = true) :
    StretchBoundOf entries rows columns stretch := by
  simp only [gramIterationFitsOf, Bool.and_eq_true, decide_eq_true_eq] at fits
  refine ⟨fits.1, fun v => ?_⟩
  rw [sumSquaresOver_product]
  exact quadraticForm_le_of_repeatedSquare rows v steps (gramMatrixOf entries columns)
    (gramMatrixOf_symmetric entries columns) (stretch * stretch) (Int.mul_nonneg fits.1 fits.1)
    fits.2

/-! ## 4. An array of rows -/

/-- The Gram test for the matrix whose rows are the entries of the array `matrix`. -/
def gramIterationFits (matrix : Matrix) (rows columns steps : Nat) (stretch : Int) : Bool :=
  gramIterationFitsOf (fun row column => (matrix.entry row).entry column) rows columns steps stretch

/-! ## 5. The test on two small matrices

The test can say yes and can say no, and a squaring can turn a no into a yes. The matrix with the
rows (30, 0) and (0, 40) stretches by 40 at most: 43 passes without a squaring, 41 only after one,
and 40 does not pass after two. The matrix with the rows (3, 4) and (4, 3) stretches by 7 at most:
without a squaring 8 passes and 7 does not. -/

example : gramIterationFits #[#[30, 0], #[0, 40]] 2 2 0 43 = true := by decide
example : gramIterationFits #[#[30, 0], #[0, 40]] 2 2 0 41 = false := by decide
example : gramIterationFits #[#[30, 0], #[0, 40]] 2 2 1 41 = true := by decide
example : gramIterationFits #[#[30, 0], #[0, 40]] 2 2 2 40 = false := by decide
example : gramIterationFits #[#[3, 4], #[4, 3]] 2 2 0 8 = true := by decide
example : gramIterationFits #[#[3, 4], #[4, 3]] 2 2 0 7 = false := by decide

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.stretchBoundOf_of_gramIterationFitsOf
