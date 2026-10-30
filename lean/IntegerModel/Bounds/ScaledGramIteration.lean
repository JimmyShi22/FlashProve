-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/ScaledGramIteration.lean

The test of IntegerModel/Bounds/GramIteration.lean with small numbers: after each product the matrix
is replaced by a given matrix of small whole numbers, and the test bounds what that costs.
- `ScaledLevel`: a given `matrix`, a `scale`, an `error` and a `bound`; below they are written `A`,
  `c`, `t` and `b`.
- `scaledChainFits size levels computed limit`. With no level left: `0 ≤ limit`, and the sum of the
  squares of the entries of `computed` is at most `limit * limit`. With a level: `c`, `t` and `b`
  are not negative; the sum of the squares of the entries of `computed - c * A` is at most `t * t`;
  `c * b + t ≤ limit`; and the other levels fit for the transpose of `A` times `A` (`transposeGram`)
  and the limit `b * b`.
- `quadraticForm_le_of_scaledChainFits`: if that test says yes, the quadratic form of `computed` at
  any vector is at most `limit` times the vector's squared length.
- `scaledGramIterationFitsOf entries rows columns levels stretch`: `0 ≤ stretch`, and the chain fits
  for the matrix times its transpose (`gramMatrixOf`) and the limit `stretch * stretch`.
- `stretchBoundOf_of_scaledGramIterationFitsOf`: if the test says yes, then
  `StretchBoundOf entries rows columns stretch` holds.
- `scaledGramIterationFits matrix rows columns levels stretch`: the test for the entries of an array
  of rows.
Nothing is asked of where the given matrices come from: a wrong one makes the test say no, or costs
sharpness, and never makes the theorem false. They need not be symmetric. For a symmetric `A` the
transpose of `A` times `A` is the square of `A` (`transposeGram_eq_squareMatrix`). With no level the
test is `gramIterationFitsOf` without a squaring (`scaledGramIterationFitsOf_nil`).
What it buys, as a reckoning and no theorem: if the entries of a given matrix are below `2 ^ 24` in
absolute value and there are at most 5,120 rows (the stream's width at the sizes of
VerifiableInference/ModelWeights.lean), then every entry of the transpose of that matrix times it is
below `2 ^ 61`. In the exact iteration the entries have about twice as many digits after each
squaring. The sums of squares that the test compares are larger than the entries.
On the cost, by reading the definitions and not by a measurement: the matrices are functions and
nothing is stored, as in the exact iteration. But each level's product is formed from a given matrix
and not from a computed one, so the cost does not multiply from level to level: a level takes about
`size ^ 3` products, times a small constant. The first level reads the matrix times its transpose,
which takes about `rows ^ 2` times `columns` products.
Limits: the theorem goes one way: a `stretch` that fails with given levels may still be a bound. How
sharp the test is with well chosen levels is not stated here. The levels are given, not computed
here. The file says of no matrix of a model that it passes. It imports Lean's core and the model's
own files.
-/
import IntegerModel.Bounds.GramIteration

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-! ## 1. The quadratic form: sums, and the two bounds -/

/-- A sum of terms `a * f k + g k`, taken apart. -/
private theorem sumOver_scaled_add (n : Nat) (a : Int) (f g : Nat → Int) :
    sumOver n (fun k => a * f k + g k) = a * sumOver n f + sumOver n g := by
  induction n with
  | zero => simp only [sumOver, Int.mul_zero, Int.add_zero]
  | succ n step => simp only [sumOver]; rw [step]; grind

/-- The quadratic form of `scale * A + E` is `scale` times that of `A` plus that of `E`. -/
theorem quadraticForm_scaled_add (size : Nat) (scale : Int) (A E : Nat → Nat → Int)
    (v : Nat → Int) :
    quadraticForm size (fun row column => scale * A row column + E row column) v =
      scale * quadraticForm size A v + quadraticForm size E v := by
  have applied : applyMatrix size (fun row column => scale * A row column + E row column) v =
      fun row => scale * applyMatrix size A v row + applyMatrix size E v row := by
    funext row
    have terms : (fun k => (scale * A row k + E row k) * v k) =
        fun k => scale * (A row k * v k) + E row k * v k := funext fun k => by grind
    show sumOver size (fun k => (scale * A row k + E row k) * v k) = _
    rw [terms, sumOver_scaled_add]
    rfl
  have terms : (fun row => v row * (scale * applyMatrix size A v row + applyMatrix size E v row)) =
      fun row => scale * (v row * applyMatrix size A v row) + v row * applyMatrix size E v row :=
    funext fun row => by grind
  unfold quadraticForm
  rw [applied, terms, sumOver_scaled_add]

/-- From a bound on a square to a bound on the number, in the form that both bounds below use. -/
private theorem le_of_square_le_of_middle_le {form length middle bound : Int}
    (lengthNonneg : 0 ≤ length) (boundNonneg : 0 ≤ bound) (square : form * form ≤ length * middle)
    (small : middle ≤ bound * bound * length) : form ≤ bound * length := by
  apply le_of_square_le (Int.mul_nonneg boundNonneg lengthNonneg)
  have scaled := Int.mul_le_mul_of_nonneg_left small lengthNonneg
  have same : length * (bound * bound * length) = bound * length * (bound * length) := by grind
  omega

/-- If the sum of the squares of the entries of `G` is at most `bound * bound`, the quadratic form
of `G` at `v` is at most `bound` times the squared length of `v`. `G` need not be symmetric. -/
theorem quadraticForm_le_of_sumSquaresOfEntries (size : Nat) (G : Nat → Nat → Int) (v : Nat → Int)
    (bound : Int) (boundNonneg : 0 ≤ bound)
    (fits : sumSquaresOfEntries size G ≤ bound * bound) :
    quadraticForm size G v ≤ bound * sumSquaresOver size v :=
  le_of_square_le_of_middle_le (sumSquaresOver_nonneg size v) boundNonneg
    (square_quadraticForm_le size G v)
    (Int.le_trans (sumSquaresOver_applyMatrix_le size G v)
      (Int.mul_le_mul_of_nonneg_right fits (sumSquaresOver_nonneg size v)))

/-- The transpose of the `size` by `size` matrix, times the matrix. -/
def transposeGram (size : Nat) (matrix : Nat → Nat → Int) : Nat → Nat → Int :=
  fun row column => sumOver size fun middle => matrix middle row * matrix middle column

/-- For a symmetric `A` the transpose of `A` times `A` is the square of `A`. -/
theorem transposeGram_eq_squareMatrix (size : Nat) (A : Nat → Nat → Int)
    (symmetric : ∀ row column, A row column = A column row) :
    transposeGram size A = squareMatrix size A :=
  funext fun row => funext fun column =>
    congrArg (sumOver size) (funext fun k => by rw [symmetric k row])

/-- The squared length of `A` times `v` is the quadratic form of the transpose of `A` times `A` at
`v`. `A` need not be symmetric. -/
theorem sumSquaresOver_applyMatrix_eq_transposeGram (size : Nat) (A : Nat → Nat → Int)
    (v : Nat → Int) :
    sumSquaresOver size (applyMatrix size A v) = quadraticForm size (transposeGram size A) v := by
  have turned : applyMatrix size A v = fun column => sumOver size fun row => v row * A column row :=
    funext fun column => congrArg (sumOver size) (funext fun _ => Int.mul_comm _ _)
  rw [turned]
  exact sumSquaresOver_product (fun row column => A column row) size size v

/-- If the quadratic form of the transpose of `A` times `A` at `v` is at most `bound * bound` times
the squared length of `v`, that of `A` is at most `bound` times the squared length. -/
theorem quadraticForm_le_of_transposeGram (size : Nat) (A : Nat → Nat → Int) (v : Nat → Int)
    (bound : Int) (boundNonneg : 0 ≤ bound)
    (squared : quadraticForm size (transposeGram size A) v ≤
      bound * bound * sumSquaresOver size v) :
    quadraticForm size A v ≤ bound * sumSquaresOver size v := by
  have square := square_quadraticForm_le size A v
  rw [sumSquaresOver_applyMatrix_eq_transposeGram] at square
  exact le_of_square_le_of_middle_le (sumSquaresOver_nonneg size v) boundNonneg square squared

/-! ## 2. The chain of levels -/

/-- One level: a given matrix, and three given numbers. -/
structure ScaledLevel where
  matrix : Nat → Nat → Int  -- A: stands, times the scale, for the matrix that was computed
  scale : Int               -- c
  error : Int               -- t: at or above the length of all entries of `computed - c * A`
  bound : Int               -- b: the quadratic form of A is at most b times the squared length

/-- **The test of a chain.** Is the quadratic form of `computed` at most `limit` times the squared
length, as far as the given levels show? -/
def scaledChainFits (size : Nat) : List ScaledLevel → (Nat → Nat → Int) → Int → Bool
  | [], computed, limit =>
    decide (0 ≤ limit) && decide (sumSquaresOfEntries size computed ≤ limit * limit)
  | level :: rest, computed, limit =>
    decide (0 ≤ level.scale) && decide (0 ≤ level.error) && decide (0 ≤ level.bound)
    && decide (sumSquaresOfEntries size
        (fun row column => computed row column - level.scale * level.matrix row column) ≤
      level.error * level.error)
    && decide (level.scale * level.bound + level.error ≤ limit)
    && scaledChainFits size rest (transposeGram size level.matrix) (level.bound * level.bound)

/-- **A chain that passes bounds the quadratic form.** -/
theorem quadraticForm_le_of_scaledChainFits (size : Nat) (v : Nat → Int)
    (levels : List ScaledLevel) :
    ∀ (computed : Nat → Nat → Int) (limit : Int)
      (_ : scaledChainFits size levels computed limit = true),
      quadraticForm size computed v ≤ limit * sumSquaresOver size v := by
  have lengthNonneg := sumSquaresOver_nonneg size v
  induction levels with
  | nil =>
    intro computed limit fits
    simp only [scaledChainFits, Bool.and_eq_true, decide_eq_true_eq] at fits
    exact quadraticForm_le_of_sumSquaresOfEntries size computed v limit fits.1 fits.2
  | cons level rest step =>
    intro computed limit fits
    simp only [scaledChainFits, Bool.and_eq_true, decide_eq_true_eq] at fits
    obtain ⟨⟨⟨⟨⟨scaleNonneg, errorNonneg⟩, boundNonneg⟩, errorFits⟩, limitFits⟩, restFits⟩ := fits
    have given := quadraticForm_le_of_transposeGram size level.matrix v level.bound boundNonneg
      (step _ _ restFits)
    have rest := quadraticForm_le_of_sumSquaresOfEntries size _ v level.error errorNonneg errorFits
    have parts : computed = fun row column => level.scale * level.matrix row column +
        (computed row column - level.scale * level.matrix row column) :=
      funext fun row => funext fun column => by omega
    have split := quadraticForm_scaled_add size level.scale level.matrix
      (fun row column => computed row column - level.scale * level.matrix row column) v
    rw [← parts] at split
    have scaled := Int.mul_le_mul_of_nonneg_left given scaleNonneg
    have limited := Int.mul_le_mul_of_nonneg_right limitFits lengthNonneg
    have same : (level.scale * level.bound + level.error) * sumSquaresOver size v =
        level.scale * (level.bound * sumSquaresOver size v) +
          level.error * sumSquaresOver size v := by grind
    omega

/-! ## 3. The matrix with given entries -/

/-- **The scaled Gram test.** Is `stretch` not negative, and does the chain of the given levels fit
for the matrix times its transpose and the limit `stretch * stretch`? -/
def scaledGramIterationFitsOf (entries : Nat → Nat → Int) (rows columns : Nat)
    (levels : List ScaledLevel) (stretch : Int) : Bool :=
  decide (0 ≤ stretch) &&
    scaledChainFits rows levels (gramMatrixOf entries columns) (stretch * stretch)

/-- **A matrix that passes the scaled Gram test stretches no vector by more than `stretch`.** -/
theorem stretchBoundOf_of_scaledGramIterationFitsOf (entries : Nat → Nat → Int)
    (rows columns : Nat) (levels : List ScaledLevel) (stretch : Int)
    (fits : scaledGramIterationFitsOf entries rows columns levels stretch = true) :
    StretchBoundOf entries rows columns stretch := by
  simp only [scaledGramIterationFitsOf, Bool.and_eq_true, decide_eq_true_eq] at fits
  refine ⟨fits.1, fun v => ?_⟩
  rw [sumSquaresOver_product]
  exact quadraticForm_le_of_scaledChainFits rows v levels _ _ fits.2

/-- With no level the test is the exact test without a squaring. -/
theorem scaledGramIterationFitsOf_nil (entries : Nat → Nat → Int) (rows columns : Nat)
    (stretch : Int) :
    scaledGramIterationFitsOf entries rows columns [] stretch =
      gramIterationFitsOf entries rows columns 0 stretch := by
  have power : (stretch * stretch) ^ (2 ^ (0 + 1)) = stretch * stretch * (stretch * stretch) := by
    show (stretch * stretch) ^ 2 = _
    rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  have nonneg : decide (0 ≤ stretch * stretch) = true := decide_eq_true (square_nonneg stretch)
  simp only [scaledGramIterationFitsOf, scaledChainFits, gramIterationFitsOf, gramPowerOf,
    repeatedSquare, power, nonneg, Bool.true_and]

/-! ## 4. An array of rows -/

/-- The scaled Gram test for the matrix whose rows are the entries of the array `matrix`. -/
def scaledGramIterationFits (matrix : Matrix) (rows columns : Nat) (levels : List ScaledLevel)
    (stretch : Int) : Bool :=
  scaledGramIterationFitsOf (fun row column => (matrix.entry row).entry column) rows columns levels
    stretch

/-- With no level the test is the exact test without a squaring. -/
theorem scaledGramIterationFits_nil (W : Matrix) (rows columns : Nat) (stretch : Int) :
    scaledGramIterationFits W rows columns [] stretch =
      gramIterationFits W rows columns 0 stretch :=
  scaledGramIterationFitsOf_nil _ rows columns stretch

/-! ## 5. The test on a small matrix

The matrix with the rows (300, 0) and (0, 400) stretches by 400 at most; times its transpose it has
the diagonal 90,000 and 160,000.
- With no level 429 passes and 428 does not.
- With one level, the diagonal divided by 7 and rounded, 405 passes and 404 does not.
- With a second level, the squares of the first divided by 1,000 and rounded, 401 passes and 400
  does not.
- The number 399 is no bound. A level with 22,000 in the place of 22,857 and the error 2 meets the
  line on the limit, and the chain after it fits; the line on the error says no. With 6,001, an
  error that is true, the line on the limit says no. -/

/-- The 2 by 2 matrix with the diagonal `first`, `second`. -/
private def twoByTwo (first second : Int) : Nat → Nat → Int :=
  fun row column => if row = column then (if row = 0 then first else second) else 0

example : scaledGramIterationFitsOf (twoByTwo 300 400) 2 2 [] 429 = true := by decide
example : scaledGramIterationFitsOf (twoByTwo 300 400) 2 2 [] 428 = false := by decide
example : scaledGramIterationFitsOf (twoByTwo 300 400) 2 2
    [⟨twoByTwo 12857 22857, 7, 2, 23409⟩] 405 = true := by decide
example : scaledGramIterationFitsOf (twoByTwo 300 400) 2 2
    [⟨twoByTwo 12857 22857, 7, 2, 23409⟩] 404 = false := by decide
example : scaledGramIterationFitsOf (twoByTwo 300 400) 2 2
    [⟨twoByTwo 12857 22857, 7, 2, 22886⟩, ⟨twoByTwo 165302 522442, 1000, 635, 523747⟩] 401 =
      true := by decide
example : scaledGramIterationFitsOf (twoByTwo 300 400) 2 2
    [⟨twoByTwo 12857 22857, 7, 2, 22886⟩, ⟨twoByTwo 165302 522442, 1000, 635, 523747⟩] 400 =
      false := by decide
example : scaledGramIterationFitsOf (twoByTwo 300 400) 2 2
    [⟨twoByTwo 12857 22000, 7, 2, 22742⟩] 399 = false := by decide
example : (7 * 22742 + 2 : Int) ≤ 399 * 399 := by decide
example : scaledChainFits 2 [] (transposeGram 2 (twoByTwo 12857 22000)) (22742 * 22742) = true := by
  decide
example : sumSquaresOfEntries 2 (fun row column => gramMatrixOf (twoByTwo 300 400) 2 row column -
    7 * twoByTwo 12857 22000 row column) = 6000 * 6000 + 1 := by decide
example : scaledGramIterationFitsOf (twoByTwo 300 400) 2 2
    [⟨twoByTwo 12857 22000, 7, 6001, 22742⟩] 399 = false := by decide

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.stretchBoundOf_of_scaledGramIterationFitsOf
#print axioms IntegerTransformer.Bounds.scaledGramIterationFitsOf_nil
#print axioms IntegerTransformer.Bounds.quadraticForm_le_of_scaledChainFits
