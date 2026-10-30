-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/LeastBoundLemmas.lean

What `leastBoundWorstCaseCheck` (IntegerModel/Bounds/LeastBoundCheck.lean) is made of: bounds on
single steps, each with its proof. Seven parts.
1. `length_of_stretchBoundOf`: a matrix with `StretchBoundOf` makes a vector at most `stretch` times
   as long. The matrix is given by its entries, so it may be a slice or have scaled columns.
2. `leastOver`: the least of a start value and of `boundAt tau` over a list; `le_leastOver`.
3. The ball as a fraction. `Ball` is a numerator and a shift; `InBall ball vector` says that
   `vector` is at most `numerator / 2^shift` long; `Ball.radius` is that fraction rounded up.
   `leastColumnBound` bounds one column's sum of products for every input in the box and the ball:
   the least of the box's bound, the ball's bound, and the bound from the two together for each
   `tau` of a list, each rounded down (`product_read_le_leastColumnBound`). `normBall` is the ball
   in which a norm's output lies, from a bound on the length of the row that the norm reads
   (`norm_out_inBall`); no range condition is among its premises. The routed expert's input lies in
   the same ball (`routedExpert_input_inFineBall`).
4. Sums over a product of two ranges: `sumOver_blocks`, `length_of_blocks`.
5. A pair of columns. `turn_square_le`: each entry of a pair turned by `(c, s)` has a square of at
   most `c^2 + s^2` times the pair's sum of squares. `pair_squares_le`: the images of a vector under
   two columns have a sum of squares of at most `lambda` times the vector's, if `lambda` dominates
   the columns' 2 by 2 Gram matrix.
6. `length_mean`: a rounded mean, with weights that are not negative, of vectors at most `V` long is
   at most `V + sqrt(width) / 2` long, in whole numbers rounded up.
7. `siluBoundWithin`: the largest absolute value of the SiLU table on the keys `-reach .. reach`;
   `magnitude_gateKeyOf_le`: the key that is read is no larger than the wide gate key.
Limits: each bound is an upper bound; nothing is said on how near it is to the largest value. The
file imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.DualColumnBound
import IntegerModel.Bounds.ScaledGramIteration

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-! ## 1. A stretch bound for a matrix that is given by its entries -/

/-- A matrix with a stretch bound makes a vector at most `stretch` times as long. -/
theorem length_of_stretchBoundOf {entries : Nat → Nat → Int} {rows columns : Nat} {stretch X : Int}
    {v : Nat → Int} (bound : StretchBoundOf entries rows columns stretch)
    (h : LengthWithin rows v X) :
    LengthWithin columns (fun column => sumOver rows fun row => v row * entries row column)
      (stretch * X) := by
  refine ⟨Int.mul_nonneg bound.1 h.1, ?_⟩
  have first := bound.2 v
  have second := Int.mul_le_mul_of_nonneg_left h.2 (square_nonneg stretch)
  have e : stretch * X * (stretch * X) = stretch * stretch * (X * X) := by grind
  omega

/-! ## 2. The least of several bounds -/

/-- The least of `start` and `boundAt tau` over the list. -/
def leastOver : List Int → (Int → Int) → Int → Int
  | [], _, start => start
  | tau :: rest, boundAt, start => min (boundAt tau) (leastOver rest boundAt start)

/-- What is at most the start value and at most the bound at every `tau` is at most the least of
them. -/
theorem le_leastOver (v : Int) (taus : List Int) (f : Int → Int) (start : Int) (h0 : v ≤ start)
    (h : ∀ tau, v ≤ f tau) : v ≤ leastOver taus f start := by
  induction taus with
  | nil => exact h0
  | cons tau rest ih =>
    simp only [leastOver]
    have := h tau
    omega

/-! ## 3. The ball as a fraction, and the bound on one column's sum -/

/-- A ball whose radius is the fraction `numerator / 2^shift`. It is called the fine ball where the
ball of a whole radius (IntegerModel/Bounds/LengthCheck.lean) is near. -/
structure Ball where
  numerator : Int
  shift : Nat

/-- The vector is at most `numerator / 2^shift` long. -/
def InBall (ball : Ball) (vector : IntegerVector) : Prop :=
  LengthWithin vector.size (fun coordinate => 2 ^ ball.shift * vector.entry coordinate)
    ball.numerator

/-- The radius, rounded up to a whole number. -/
def Ball.radius (ball : Ball) : Int := shiftUp ball.numerator ball.shift

/-- A vector in a ball is at most as long as the ball's radius, rounded up. -/
theorem rowLength_of_inBall {ball : Ball} {a : IntegerVector} (h : InBall ball a) :
    RowLengthWithin ball.radius a :=
  length_unscale (Int.pow_pos (by decide)) (shiftUp_nonneg h.1 _)
    (length_of_le h (shiftUp_spec _ _))

/-- A common factor of the first vector comes out of a sum of products. -/
theorem sumOver_scaled_inner (n : Nat) (D : Int) (f g : Nat → Int) :
    (sumOver n fun k => D * f k * g k) = D * sumOver n fun k => f k * g k := by
  rw [← sumOver_mul_left]
  congr 1
  funext k
  grind

/-- From a bound on `D * v` to a bound on `v`, rounded down. -/
theorem magnitude_le_ediv_of_scaled {D v I : Int} (positive : 0 < D)
    (h : magnitude (D * v) ≤ I) : magnitude v ≤ I / D := by
  apply (Int.le_ediv_iff_mul_le positive).mpr
  rw [magnitude_mul] at h
  have same : magnitude D = D := by unfold magnitude; omega
  rw [same, Int.mul_comm] at h
  exact h

/-- Cauchy-Schwarz for a vector in a ball whose radius is a fraction. -/
theorem magnitude_inner_le_root_scaled {n : Nat} {f : Nat → Int} {X D : Int} (positive : 0 < D)
    (hf : LengthWithin n (fun k => D * f k) X) (g : Nat → Int) :
    magnitude (sumOver n fun k => f k * g k) ≤ integerSquareRoot (X * X * sumSquaresOver n g).toNat / D := by
  have whole := magnitude_inner_le_root hf g
  rw [sumOver_scaled_inner] at whole
  exact magnitude_le_ediv_of_scaled positive whole

/-- The ball and the box together, for a ball whose radius is a fraction. -/
theorem magnitude_inner_le_dual_scaled {n : Nat} {a : Nat → Int} {X D bound tau : Int}
    (u : Nat → Int) (box : ∀ k, k < n → magnitude (a k) ≤ bound) (scale : 0 < D)
    (ball : LengthWithin n (fun k => D * a k) X) (positive : 0 < tau) (boundPositive : 0 < bound) :
    magnitude (sumOver n fun k => a k * u k) ≤
      (tau * tau * (X * X) + D * bound * (D * bound) * sumOver n fun k => cappedSquare tau (u k))
        / (2 * tau * (D * bound)) / D := by
  have whole := magnitude_inner_le_dual u (a := fun k => D * a k) (bound := D * bound)
    (fun k hk => by
      rw [magnitude_mul]
      have same : magnitude D = D := by unfold magnitude; omega
      rw [same]
      exact Int.mul_le_mul_of_nonneg_left (box k hk) (by omega))
    ball positive (Int.mul_pos scale boundPositive)
  rw [sumOver_scaled_inner] at whole
  exact magnitude_le_ediv_of_scaled scale whole

/-- The ball's bound on one column's sum, rounded down. -/
def fineBallColumnBound (ball : Ball) (matrix : Matrix) (rows column : Nat) : Int :=
  integerSquareRoot (ball.numerator * ball.numerator * columnSquares matrix rows column).toNat / 2 ^ ball.shift

/-- The bound from the ball and the box together for one `tau`, rounded down; the box's bound for a
`tau` that is not positive. -/
def dualColumnBound (ball : Ball) (tau : Int) (matrix : Matrix) (rows column : Nat) : Int :=
  if 0 < tau then
    (tau * tau * (ball.numerator * ball.numerator)
        + 2 ^ ball.shift * activationBound * (2 ^ ball.shift * activationBound)
          * sumOver rows fun row => cappedSquare tau ((matrix.entry row).entry column))
      / (2 * tau * (2 ^ ball.shift * activationBound)) / 2 ^ ball.shift
  else boxColumnBound matrix rows column

/-- The bound on one column's sum: the least of the box's, the ball's, and the two together for each
`tau` of the list. -/
def leastColumnBound (taus : List Int) (ball : Ball) (matrix : Matrix) (rows column : Nat) : Int :=
  leastOver taus (fun tau => dualColumnBound ball tau matrix rows column)
    (min (boxColumnBound matrix rows column) (fineBallColumnBound ball matrix rows column))

/-- The sum that a read of a product stands for; a read outside is 0. -/
theorem product_read_le_of_sum (a : IntegerVector) (W : Matrix) (outputs j : Nat) (b : Int)
    (h : magnitude (sumOver a.size fun k => a.entry k * (W.entry k).entry j) ≤ b) :
    magnitude ((product a W outputs).entry j) ≤ b := by
  by_cases inside : j < outputs
  · unfold product
    rw [tabulate_read _ _ _ inside]
    exact h
  · rw [entry_outside _ j (by rw [size_product]; exact inside)]
    exact Int.le_trans (by decide) (Int.le_trans (magnitude_nonneg _) h)

/-- **The bound on one column's sum.** Every read of a product whose input lies in the box and in
the ball is within `leastColumnBound`. -/
theorem product_read_le_leastColumnBound (taus : List Int) (a : IntegerVector) (W : Matrix)
    (outputs width : Nat) (ball : Ball) (size : a.size = width) (box : InBox a)
    (inBall : InBall ball a) (j : Nat) :
    magnitude ((product a W outputs).entry j) ≤ leastColumnBound taus ball W width j := by
  have scale : (0 : Int) < 2 ^ ball.shift := Int.pow_pos (by decide)
  have fromBox := product_read_le a W outputs width size box j
  unfold leastColumnBound
  apply le_leastOver
  · have fromBall : magnitude ((product a W outputs).entry j) ≤
        fineBallColumnBound ball W width j := by
      apply product_read_le_of_sum
      unfold fineBallColumnBound columnSquares
      rw [← size]
      exact magnitude_inner_le_root_scaled scale inBall _
    omega
  · intro tau
    unfold dualColumnBound
    split
    · next positive =>
      apply product_read_le_of_sum
      rw [← size]
      exact magnitude_inner_le_dual_scaled (fun k => (W.entry k).entry j) (fun k _ => box k) scale
        inBall positive (by decide : 0 < activationBound)
    · exact fromBox

/-- The ball in which a norm's output lies, if the row that it reads is at most `rowLength` long.
Its radius is the fraction `numerator / 2^K`. The numerator is the sum of `2^M`; of half the largest
root that such a row can have and of `2^M / integerSquareRoot eps`, each rounded down, and 1 for the two; and of
the root of `d * 4^(K-1)`, rounded down, and 1 (`rootUp`). In real numbers that is at most
`2^(M-K) (1 + 1 / integerSquareRoot eps) + root / 2^(K+1) + sqrt(d) / 2 + 2 / 2^K`. -/
def normBall (width bits shift : Nat) (eps rowLength : Int) : Ball where
  numerator := 2 ^ bits + (integerSquareRoot (rowLength * rowLength + eps).toNat : Int) / 2
    + 2 ^ bits / (integerSquareRoot eps.toNat : Int) + 1
    + rootUp (width * (2 ^ (shift - 1) * 2 ^ (shift - 1)))
  shift := shift

/-- **The ball.** A norm's output lies in `normBall`, if the row that the norm reads is at most `X`
long. No range condition is a premise. -/
theorem norm_out_inBall (bits shift : Nat) (eps : Int) (x : IntegerVector) (X : Int) (eps_pos : 1 ≤ eps)
    (shift_pos : 1 ≤ shift) (h : RowLengthWithin X x) :
    InBall (normBall x.size bits shift eps X) (rmsNorm bits shift eps x).out := by
  unfold RowLengthWithin at h
  unfold InBall normBall
  dsimp only
  rw [(size_rmsNorm bits shift eps x).2]
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
  have error : LengthWithin x.size
      (fun k => 2 ^ shift * roundShift (R * x.entry k) shift - R * x.entry k)
      (rootUp (x.size * (2 ^ (shift - 1) * 2 ^ (shift - 1)))) := by
    refine ⟨(rootUp_spec _).1, Int.le_trans ?_ (rootUp_spec _).2⟩
    rw [← sumOver_const]
    exact sumOver_le_sumOver _ _ _ fun k _ =>
      square_le_square _ _ (roundShift_error (R * x.entry k) shift shift_pos)
  have together := length_add raised error
  have same : (fun k => R * x.entry k
    + (2 ^ shift * roundShift (R * x.entry k) shift - R * x.entry k))
      = fun k => 2 ^ shift * roundShift (R * x.entry k) shift := by
    funext k
    omega
  rw [same] at together
  refine length_of_entries together fun k hk => ?_
  rw [outAt k hk, Int.mul_comm (x.entry k) R]
  have clamped := Int.mul_le_mul_of_nonneg_left
    (clamp_square_le (roundShift (R * x.entry k) shift) activationBound (by decide))
    (square_nonneg ((2 : Int) ^ shift))
  generalize clamp (roundShift (R * x.entry k) shift) activationBound = c at *
  generalize roundShift (R * x.entry k) shift = q at *
  generalize (2 : Int) ^ shift = D at *
  have e1 : D * c * (D * c) = D * D * (c * c) := by grind
  have e2 : D * q * (D * q) = D * D * (q * q) := by grind
  omega

/-- A vector that is entry by entry no larger lies in the same ball. -/
theorem inBall_of_entries {ball : Ball} {a b : IntegerVector} (size : b.size = a.size) (h : InBall ball a)
    (small : ∀ k, k < a.size → magnitude (b.entry k) ≤ magnitude (a.entry k)) : InBall ball b := by
  unfold InBall at *
  rw [size]
  refine length_of_entries h fun k hk => ?_
  have square := square_le_square _ _ (small k hk)
  rw [magnitude_mul_self] at square
  have scaled := Int.mul_le_mul_of_nonneg_left square (square_nonneg ((2 : Int) ^ ball.shift))
  generalize (2 : Int) ^ ball.shift = D at *
  have e1 : D * b.entry k * (D * b.entry k) = D * D * (b.entry k * b.entry k) := by grind
  have e2 : D * a.entry k * (D * a.entry k) = D * D * (a.entry k * a.entry k) := by grind
  omega

/-- The routed expert's input lies in the normed row's ball. -/
theorem routedExpert_input_inFineBall (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (m : IntegerVector) (ball : Ball) (box : InBox m) (inBall : InBall ball m)
    (fits : routedInputFits tables = true) : InBall ball (routedExpert s p tables w m).input := by
  have made : (routedExpert s p tables w m).input =
      m.map fun mk => roundShift ((routedExpert s p tables w m).scale * mk) 16 := rfl
  simp only [routedInputFits, decide_eq_true_eq] at fits
  apply inBall_of_entries (by rw [made, Array.size_map]) inBall
  intro k inside
  rw [made, map_read _ _ _ inside]
  exact magnitude_scaled_le _ _ (m.entry k) fits
    (magnitude_read_le tables.sigmoid _ : magnitude (routedExpert s p tables w m).scale ≤ _) (box k)

/-! ## 4. Sums over a product of two ranges -/

/-- A sum over `a + b` terms: the first `a`, then the other `b`. -/
theorem sumOver_append (a b : Nat) (f : Nat → Int) :
    sumOver (a + b) f = sumOver a f + sumOver b fun c => f (a + c) := by
  induction b with
  | zero => simp [sumOver]
  | succ b ih =>
    rw [← Nat.add_assoc]
    simp only [sumOver, ih]
    omega

/-- A sum over `n * m` terms, as a sum over `n` blocks of `m` terms. -/
theorem sumOver_blocks (n m : Nat) (f : Nat → Int) :
    sumOver (n * m) f = sumOver n fun h => sumOver m fun c => f (h * m + c) := by
  induction n with
  | zero => simp [sumOver]
  | succ n ih =>
    rw [Nat.succ_mul, sumOver_append, ih]
    simp only [sumOver]

/-- Blocks of `m` entries, block `b` at most `length b` long: the whole. -/
theorem length_of_blocks {n m : Nat} {f : Nat → Int} {length : Nat → Int}
    (h : ∀ b, b < n → LengthWithin m (fun c => f (b * m + c)) (length b)) :
    LengthWithin (n * m) f (rootUp (sumSquaresOver n length)) := by
  refine ⟨(rootUp_spec _).1, Int.le_trans ?_ (rootUp_spec _).2⟩
  unfold sumSquaresOver
  rw [sumOver_blocks]
  exact sumOver_le_sumOver _ _ _ fun b hb => (h b hb).2

/-! ## 5. A pair of columns: the rotary step -/

/-- Each entry of a pair turned by (c, s) is at most the root of c^2 + s^2 times the pair's length.
-/
theorem turn_square_le (c s a0 a1 : Int) :
    (c * a0 - s * a1) * (c * a0 - s * a1) ≤ (c * c + s * s) * (a0 * a0 + a1 * a1)
    ∧ (s * a0 + c * a1) * (s * a0 + c * a1) ≤ (c * c + s * s) * (a0 * a0 + a1 * a1) := by
  constructor
  · have square := square_nonneg (s * a0 + c * a1)
    have e : (c * c + s * s) * (a0 * a0 + a1 * a1) =
        (c * a0 - s * a1) * (c * a0 - s * a1) + (s * a0 + c * a1) * (s * a0 + c * a1) := by grind
    omega
  · have square := square_nonneg (c * a0 - s * a1)
    have e : (c * c + s * s) * (a0 * a0 + a1 * a1) =
        (c * a0 - s * a1) * (c * a0 - s * a1) + (s * a0 + c * a1) * (s * a0 + c * a1) := by grind
    omega

/-- `lambda` dominates the 2 x 2 Gram matrix with diagonal `n0, n1` and off-diagonal `p`. -/
theorem gram_form_le (n0 n1 p lambda x y : Int) (h0 : n0 ≤ lambda) (h1 : n1 ≤ lambda)
    (determinant : p * p ≤ (lambda - n0) * (lambda - n1)) :
    x * x * n0 + 2 * (x * y * p) + y * y * n1 ≤ lambda * (x * x + y * y) := by
  have cross : 2 * (p * (x * y)) ≤ (lambda - n0) * (x * x) + (lambda - n1) * (y * y) := by
    apply two_mul_le_add (Int.mul_nonneg (by omega) (square_nonneg x))
      (Int.mul_nonneg (by omega) (square_nonneg y))
    have scaled := Int.mul_le_mul_of_nonneg_right determinant (square_nonneg (x * y))
    have e1 : p * (x * y) * (p * (x * y)) = p * p * (x * y * (x * y)) := by grind
    have e2 : (lambda - n0) * (x * x) * ((lambda - n1) * (y * y)) =
        (lambda - n0) * (lambda - n1) * (x * y * (x * y)) := by grind
    omega
  have e1 : (lambda - n0) * (x * x) + (lambda - n1) * (y * y) =
      lambda * (x * x + y * y) - (x * x * n0 + y * y * n1) := by grind
  have e2 : p * (x * y) = x * y * p := by grind
  omega

/-- The images of a vector under two columns: the sum of their squares is at most `lambda` times the
vector's, if `lambda` dominates the columns' Gram matrix. -/
theorem pair_squares_le (n : Nat) (a u0 u1 : Nat → Int) (lambda : Int)
    (h0 : sumSquaresOver n u0 ≤ lambda) (h1 : sumSquaresOver n u1 ≤ lambda)
    (determinant : (sumOver n fun k => u0 k * u1 k) * (sumOver n fun k => u0 k * u1 k)
      ≤ (lambda - sumSquaresOver n u0) * (lambda - sumSquaresOver n u1)) :
    (sumOver n fun k => a k * u0 k) * (sumOver n fun k => a k * u0 k)
      + (sumOver n fun k => a k * u1 k) * (sumOver n fun k => a k * u1 k)
      ≤ lambda * sumSquaresOver n a := by
  generalize hx : (sumOver n fun k => a k * u0 k) = x
  generalize hy : (sumOver n fun k => a k * u1 k) = y
  have cs := cauchy_schwarz n a fun k => x * u0 k + y * u1 k
  have inner : (sumOver n fun k => a k * (x * u0 k + y * u1 k)) = x * x + y * y := by
    have split : (fun k => a k * (x * u0 k + y * u1 k)) =
        fun k => x * (a k * u0 k) + y * (a k * u1 k) := by
      funext k; grind
    rw [split, sumOver_add, sumOver_mul_left, sumOver_mul_left, hx, hy]
  have squares : sumSquaresOver n (fun k => x * u0 k + y * u1 k) =
      x * x * sumSquaresOver n u0 + 2 * (x * y * sumOver n fun k => u0 k * u1 k)
        + y * y * sumSquaresOver n u1 := by
    unfold sumSquaresOver
    have split : (fun k => (x * u0 k + y * u1 k) * (x * u0 k + y * u1 k)) =
        fun k => x * x * (u0 k * u0 k) + (2 * (x * y)) * (u0 k * u1 k) + y * y * (u1 k * u1 k) := by
      funext k; grind
    rw [split, sumOver_add, sumOver_add, sumOver_mul_left, sumOver_mul_left, sumOver_mul_left]
    grind
  rw [inner, squares] at cs
  have form := gram_form_le _ _ _ lambda x y h0 h1 determinant
  have lengthNonneg := sumSquaresOver_nonneg n a
  have lambdaNonneg : 0 ≤ lambda := Int.le_trans (sumSquaresOver_nonneg n u0) h0
  have total : 0 ≤ x * x + y * y := by
    have := square_nonneg x
    have := square_nonneg y
    omega
  generalize x * x + y * y = T at *
  have chain : T * T ≤ sumSquaresOver n a * (lambda * T) :=
    Int.le_trans cs (Int.mul_le_mul_of_nonneg_left form lengthNonneg)
  by_cases zero : T = 0
  · rw [zero]; exact Int.mul_nonneg lambdaNonneg lengthNonneg
  · have e : sumSquaresOver n a * (lambda * T) = lambda * sumSquaresOver n a * T := by grind
    rw [e] at chain
    exact Int.le_of_mul_le_mul_right chain (by omega)

/-! ## 6. A rounded mean, in length -/

/-- A sum of vectors with weights that are not negative is at most (the weights' sum) * V long. -/
theorem length_weighted_sum {count width : Nat} {weight : Nat → Int} {vector : Nat → Nat → Int}
    {V : Int} (nonneg : ∀ j, 0 ≤ weight j)
    (each : ∀ j, j < count → LengthWithin width (vector j) V) :
    LengthWithin width (fun c => sumOver count fun j => weight j * vector j c)
      (sumOver count weight * V) := by
  induction count with
  | zero =>
    simp only [sumOver]
    refine ⟨by omega, ?_⟩
    have : sumSquaresOver width (fun _ => (0 : Int)) = 0 := by
      unfold sumSquaresOver
      rw [sumOver_const]
      omega
    rw [this]
    omega
  | succ count ih =>
    simp only [sumOver]
    have below := ih fun j hj => each j (by omega)
    have last := length_scale (each count (by omega)) (nonneg count)
    have sum := length_add below last
    rw [Int.add_mul]
    exact sum

/-- A rounded mean, with weights that are not negative, of vectors at most V long is at most V +
sqrt(width) / 2 long, in whole numbers rounded up. The division is attention's. -/
theorem length_mean {count width : Nat} {weight : Nat → Int} {vector : Nat → Nat → Int} {V : Int}
    (nonneg : ∀ j, 0 ≤ weight j) (positive : 0 < sumOver count weight) (hV : 0 ≤ V)
    (each : ∀ j, j < count → LengthWithin width (vector j) V) :
    LengthWithin width
      (fun c => (2 * (sumOver count fun j => weight j * vector j c) + sumOver count weight)
        / (2 * sumOver count weight))
      (V + (rootUp width + 1) / 2) := by
  have sum := length_weighted_sum nonneg each
  generalize sumOver count weight = total at *
  generalize hacc : (fun c => sumOver count fun j => weight j * vector j c) = acc at sum
  have accAt : ∀ c, (sumOver count fun j => weight j * vector j c) = acc c := by
    intro c; rw [← hacc]
  simp only [accAt]
  have root := (rootUp_spec (width : Int)).1
  have error : ∀ c, c < width →
      magnitude (2 * total * ((2 * acc c + total) / (2 * total)) - 2 * acc c) ≤ total := by
    intro c _
    have low := Int.ediv_mul_le (2 * acc c + total) (by omega : 2 * total ≠ 0)
    have high := Int.lt_ediv_add_one_mul_self (2 * acc c + total) (by omega : 0 < 2 * total)
    rw [Int.add_mul, Int.one_mul] at high
    rw [Int.mul_comm (2 * total) _, magnitude_le_iff]
    generalize (2 * acc c + total) / (2 * total) * (2 * total) = q at *
    omega
  have errorLength := length_of_bound error (by omega)
  have doubled := length_scale sum (by omega : (0 : Int) ≤ 2)
  have together := length_add doubled errorLength
  have same : (fun c => 2 * acc c + (2 * total * ((2 * acc c + total) / (2 * total)) - 2 * acc c)) =
      fun c => 2 * total * ((2 * acc c + total) / (2 * total)) := by
    funext c
    omega
  rw [same] at together
  apply length_unscale (by omega : 0 < 2 * total) (by omega)
  apply length_of_le together
  have half : rootUp width ≤ 2 * ((rootUp width + 1) / 2) := by omega
  have scaled := Int.mul_le_mul_of_nonneg_left half (by omega : 0 ≤ total)
  have expand : 2 * total * (V + (rootUp width + 1) / 2) =
      2 * (total * V) + total * (2 * ((rootUp width + 1) / 2)) := by grind
  omega

/-! ## 7. The SiLU table on the keys that a gate can reach -/

/-- The largest absolute value of the SiLU table's entries at the keys `-reach .. reach`. -/
def siluBoundWithin (tables : Tables) (reach : Int) : Int :=
  maxUpTo (fun index => magnitude (tables.silu.read ((index : Int) - reach))) (2 * reach).toNat

/-- A read of the SiLU table at a key within `reach` is within `siluBoundWithin`. -/
theorem magnitude_silu_read_le (tables : Tables) (reach key : Int) (h : magnitude key ≤ reach) :
    magnitude (tables.silu.read key) ≤ siluBoundWithin tables reach := by
  rw [magnitude_le_iff] at h
  have at_index := (maxUpTo_spec (fun i => magnitude (tables.silu.read ((i : Int) - reach)))
    (2 * reach).toNat).1 (key + reach).toNat (by omega)
  have same : (((key + reach).toNat : Nat) : Int) - reach = key := by omega
  simp only [same] at at_index
  exact at_index

/-- The bound is not negative. -/
theorem siluBoundWithin_nonneg (tables : Tables) (reach : Int) : 0 ≤ siluBoundWithin tables reach :=
  Int.le_trans (magnitude_nonneg _)
    ((maxUpTo_spec (fun i => magnitude (tables.silu.read ((i : Int) - reach)))
      (2 * reach).toNat).1 0 (by omega))

/-- The bound on some keys is at most the largest entry of the whole table. -/
theorem siluBoundWithin_le_largest (tables : Tables) (reach : Int) :
    siluBoundWithin tables reach ≤ largestMagnitude tables.silu.entries := by
  obtain ⟨i, _, attained⟩ := (maxUpTo_spec
    (fun i => magnitude (tables.silu.read ((i : Int) - reach))) (2 * reach).toNat).2
  unfold siluBoundWithin
  rw [← attained]
  exact magnitude_read_le _ _

/-- The key at which the SiLU table is read is no larger than the wide gate key, and at most 32,640.
-/
theorem magnitude_gateKeyOf_le (wide : Int) :
    magnitude (gateKeyOf wide) ≤ magnitude wide ∧ magnitude (gateKeyOf wide) ≤ 32640 := by
  unfold gateKeyOf clamp balancedLowByte magnitude
  omega

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.length_of_stretchBoundOf
#print axioms IntegerTransformer.Bounds.le_leastOver
#print axioms IntegerTransformer.Bounds.product_read_le_leastColumnBound
#print axioms IntegerTransformer.Bounds.norm_out_inBall
#print axioms IntegerTransformer.Bounds.routedExpert_input_inFineBall
#print axioms IntegerTransformer.Bounds.length_of_blocks
#print axioms IntegerTransformer.Bounds.turn_square_le
#print axioms IntegerTransformer.Bounds.pair_squares_le
#print axioms IntegerTransformer.Bounds.length_mean
#print axioms IntegerTransformer.Bounds.magnitude_silu_read_le
#print axioms IntegerTransformer.Bounds.magnitude_gateKeyOf_le
