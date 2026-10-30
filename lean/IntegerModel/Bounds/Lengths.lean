-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Bounds.Arithmetic

/-!
# Lengths of vectors of whole numbers

A vector is "at most `X` long" if `X` is not negative and the sum of the vector's squares is at most
`X * X` (`LengthWithin`). So no root of a sum is taken, and every statement is about whole numbers.
A vector is given as a function `Nat → Int` with the number of its entries.

The file proves the Cauchy-Schwarz inequality on `sumOver` (`cauchy_schwarz`, and
`magnitude_inner_le` in the form that bounds use), the triangle inequality for lengths
(`length_add`), what a factor does to a length (`length_scale`, `length_unscale`), and what
`roundShift` does to it (`length_roundShift`): the length is divided by the power of two, and the
rounding adds at most half the root of the number of entries. Where a root or a quotient is needed,
it is rounded up to a whole number (`rootUp`, `shiftUp`).

Only Lean's core library is used. Nothing here speaks of the model.
-/

namespace IntegerTransformer.Bounds

/-- The sum of the squares of `f 0, .., f (n - 1)`. -/
def sumSquaresOver (n : Nat) (f : Nat → Int) : Int := sumOver n fun k => f k * f k

/-- The vector `f 0, .., f (n - 1)` is at most `length` long. -/
def LengthWithin (n : Nat) (f : Nat → Int) (length : Int) : Prop :=
  0 ≤ length ∧ sumSquaresOver n f ≤ length * length

/-- A whole number that is not negative and whose square is at least `a` (`rootUp_spec`): one more
than the root of `a`, rounded down. -/
def rootUp (a : Int) : Int := integerSquareRoot a.toNat + 1

/-- `a / 2^k`, rounded up. -/
def shiftUp (a : Int) (k : Nat) : Int := (a + 2 ^ k - 1) / 2 ^ k

/-- At or above the length of a vector of `count` entries after `roundShift`, if it was at most
`length` long before: `length / 2^shift + sqrt(count) / 2`, in whole numbers, rounded up. -/
def roundedLength (count : Nat) (length : Int) (shift : Nat) : Int :=
  shiftUp (length + 2 ^ (shift - 1) * rootUp count) shift

/-- For `b ≥ 0`, a number whose square is at most `b * b` is at most `b`. -/
theorem le_of_square_le {a b : Int} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b := by
  apply Int.le_of_not_gt
  intro high
  have : b * b < a * a := by
    have h1 : b * b ≤ b * a := Int.mul_le_mul_of_nonneg_left (by omega) hb
    have h2 : b * a < a * a := Int.mul_lt_mul_of_pos_right high (by omega)
    omega
  omega

/-- The inequality of the arithmetic and the geometric mean, without roots. -/
theorem two_mul_le_add {t p q : Int} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : t * t ≤ p * q) :
    2 * t ≤ p + q := by
  apply le_of_square_le (by omega)
  have square := square_nonneg (p - q)
  have e1 : (p + q) * (p + q) = (p - q) * (p - q) + 4 * (p * q) := by grind
  have e2 : 2 * t * (2 * t) = 4 * (t * t) := by grind
  omega

/-- **Cauchy-Schwarz** on `sumOver`. -/
theorem cauchy_schwarz (n : Nat) (f g : Nat → Int) :
    sumOver n (fun k => f k * g k) * sumOver n (fun k => f k * g k)
      ≤ sumSquaresOver n f * sumSquaresOver n g := by
  induction n with
  | zero => simp [sumOver, sumSquaresOver]
  | succ n ih =>
    simp only [sumOver, sumSquaresOver] at ih ⊢
    have nf : 0 ≤ sumOver n fun k => f k * f k := sumOver_nonneg _ (fun _ => square_nonneg _) _
    have ng : 0 ≤ sumOver n fun k => g k * g k := sumOver_nonneg _ (fun _ => square_nonneg _) _
    generalize sumOver n (fun k => f k * g k) = c at *
    generalize sumOver n (fun k => f k * f k) = a at *
    generalize sumOver n (fun k => g k * g k) = b at *
    generalize f n = x
    generalize g n = y
    have cross : 2 * (c * (x * y)) ≤ a * (y * y) + b * (x * x) := by
      apply two_mul_le_add (Int.mul_nonneg nf (square_nonneg y))
        (Int.mul_nonneg ng (square_nonneg x))
      have scaled := Int.mul_le_mul_of_nonneg_right ih (square_nonneg (x * y))
      have e1 : c * (x * y) * (c * (x * y)) = c * c * (x * y * (x * y)) := by grind
      have e2 : a * (y * y) * (b * (x * x)) = a * b * (x * y * (x * y)) := by grind
      omega
    have e1 : (c + x * y) * (c + x * y) = c * c + 2 * (c * (x * y)) + x * y * (x * y) := by grind
    have e2 : (a + x * x) * (b + y * y) =
        a * b + (a * (y * y) + b * (x * x)) + x * y * (x * y) := by grind
    omega

/-- A sum of squares is not negative. -/
theorem sumSquaresOver_nonneg (n : Nat) (f : Nat → Int) : 0 ≤ sumSquaresOver n f :=
  sumOver_nonneg _ (fun _ => square_nonneg _) _

/-- The Cauchy-Schwarz inequality in the form that bounds use: the inner product of two vectors is
at most the product of their lengths. -/
theorem magnitude_inner_le {n : Nat} {f g : Nat → Int} {X Y : Int} (hf : LengthWithin n f X)
    (hg : LengthWithin n g Y) : magnitude (sumOver n fun k => f k * g k) ≤ X * Y := by
  rw [magnitude_le_iff]
  have cs := cauchy_schwarz n f g
  have product : sumSquaresOver n f * sumSquaresOver n g ≤ X * X * (Y * Y) :=
    Int.mul_le_mul hf.2 hg.2 (sumSquaresOver_nonneg n g) (Int.mul_nonneg hf.1 hf.1)
  have e : X * X * (Y * Y) = X * Y * (X * Y) := by grind
  have nonneg : 0 ≤ X * Y := Int.mul_nonneg hf.1 hg.1
  generalize sumOver n (fun k => f k * g k) = c at *
  constructor
  · have : -c ≤ X * Y := le_of_square_le nonneg (by rw [Int.neg_mul_neg]; omega)
    omega
  · exact le_of_square_le nonneg (by omega)

/-- The square of a sum, summed: the two sums of squares and twice the inner product. -/
theorem sumSquaresOver_add (n : Nat) (f g : Nat → Int) :
    sumSquaresOver n (fun k => f k + g k)
      = sumSquaresOver n f + 2 * sumOver n (fun k => f k * g k) + sumSquaresOver n g := by
  induction n with
  | zero => simp [sumOver, sumSquaresOver]
  | succ n ih =>
    simp only [sumOver, sumSquaresOver] at ih ⊢
    rw [ih]
    grind

/-- **The triangle inequality** for lengths. -/
theorem length_add {n : Nat} {f g : Nat → Int} {X Y : Int} (hf : LengthWithin n f X)
    (hg : LengthWithin n g Y) : LengthWithin n (fun k => f k + g k) (X + Y) := by
  refine ⟨by have := hf.1; have := hg.1; omega, ?_⟩
  rw [sumSquaresOver_add]
  have inner := ((magnitude_le_iff _ _).mp (magnitude_inner_le hf hg)).2
  have e : (X + Y) * (X + Y) = X * X + 2 * (X * Y) + Y * Y := by grind
  have := hf.2
  have := hg.2
  omega

/-- A vector that is at most `X` long is at most `Y` long for every `Y ≥ X`. -/
theorem length_of_le {n : Nat} {f : Nat → Int} {X Y : Int} (h : LengthWithin n f X) (le : X ≤ Y) :
    LengthWithin n f Y := by
  refine ⟨by have := h.1; omega, ?_⟩
  have := Int.mul_le_mul le le h.1 (by have := h.1; omega)
  have := h.2
  omega

/-- Entry by entry smaller in absolute value: not longer. -/
theorem length_of_entries {n : Nat} {f g : Nat → Int} {X : Int} (h : LengthWithin n g X)
    (small : ∀ k, k < n → f k * f k ≤ g k * g k) : LengthWithin n f X :=
  ⟨h.1, Int.le_trans (sumOver_le_sumOver _ _ _ small) h.2⟩

/-- A factor leaves a sum of squares as its square. -/
theorem sumSquaresOver_scale (n : Nat) (c : Int) (f : Nat → Int) :
    sumSquaresOver n (fun k => c * f k) = c * c * sumSquaresOver n f := by
  induction n with
  | zero => simp [sumOver, sumSquaresOver]
  | succ n ih =>
    simp only [sumOver, sumSquaresOver] at ih ⊢
    rw [ih]
    grind

/-- A factor `c ≥ 0` multiplies the length. -/
theorem length_scale {n : Nat} {f : Nat → Int} {X c : Int} (h : LengthWithin n f X) (hc : 0 ≤ c) :
    LengthWithin n (fun k => c * f k) (c * X) := by
  refine ⟨Int.mul_nonneg hc h.1, ?_⟩
  rw [sumSquaresOver_scale]
  have := Int.mul_le_mul_of_nonneg_left h.2 (square_nonneg c)
  have e : c * X * (c * X) = c * c * (X * X) := by grind
  omega

/-- A positive factor can be taken out again. -/
theorem length_unscale {n : Nat} {f : Nat → Int} {X c : Int} (hc : 0 < c) (hX : 0 ≤ X)
    (h : LengthWithin n (fun k => c * f k) (c * X)) : LengthWithin n f X := by
  refine ⟨hX, ?_⟩
  have h2 := h.2
  rw [sumSquaresOver_scale] at h2
  have e : c * X * (c * X) = c * c * (X * X) := by grind
  rw [e] at h2
  exact Int.le_of_mul_le_mul_left h2 (Int.mul_pos hc hc)

/-- `rootUp a` is not negative, and its square is at least `a`. -/
theorem rootUp_spec (a : Int) : 0 ≤ rootUp a ∧ a ≤ rootUp a * rootUp a := by
  have spec := (isqrt_spec a.toNat).2
  unfold rootUp
  have cast : ((integerSquareRoot a.toNat + 1) * (integerSquareRoot a.toNat + 1) : Nat) =
      (((integerSquareRoot a.toNat : Int) + 1) * ((integerSquareRoot a.toNat : Int) + 1) : Int) := by simp
  have : (a.toNat : Int) < ((integerSquareRoot a.toNat : Int) + 1) * ((integerSquareRoot a.toNat : Int) + 1) := by
    rw [← cast]; exact Int.ofNat_lt.mpr spec
  constructor <;> omega

/-- A vector whose entry `k` is at most `b k` in absolute value is at most as long as the vector of
these bounds, with the root rounded up. -/
theorem length_of_bounds {n : Nat} {f b : Nat → Int} (h : ∀ k, k < n → magnitude (f k) ≤ b k) :
    LengthWithin n f (rootUp (sumSquaresOver n b)) :=
  ⟨(rootUp_spec _).1,
    Int.le_trans (sumOver_le_sumOver _ _ _ fun k hk => square_le_square _ _ (h k hk))
      (rootUp_spec _).2⟩

/-- `shiftUp a k` is at least `a / 2^k`. -/
theorem shiftUp_spec (a : Int) (k : Nat) : a ≤ 2 ^ k * shiftUp a k := by
  have pos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  unfold shiftUp
  generalize (2 : Int) ^ k = m at *
  have := Int.lt_ediv_add_one_mul_self (a + m - 1) pos
  rw [Int.add_mul, Int.one_mul, Int.mul_comm] at this
  omega

/-- The sum of `n` equal terms. -/
theorem sumOver_const (n : Nat) (c : Int) : sumOver n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumOver]
  | succ n ih =>
    simp only [sumOver, ih]
    push_cast
    grind

/-- For `a ≥ 0`, `shiftUp a k` is not negative. -/
theorem shiftUp_nonneg {a : Int} (h : 0 ≤ a) (k : Nat) : 0 ≤ shiftUp a k := by
  have pos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  unfold shiftUp
  exact Int.ediv_nonneg (by omega) (by omega)

/-- A vector of `n` entries, each at most `m` in absolute value, is at most `m * rootUp n` long. -/
theorem length_of_bound {n : Nat} {f : Nat → Int} {m : Int}
    (h : ∀ k, k < n → magnitude (f k) ≤ m) (hm : 0 ≤ m) : LengthWithin n f (m * rootUp n) := by
  have root := rootUp_spec (n : Int)
  refine ⟨Int.mul_nonneg hm root.1, ?_⟩
  have first : sumSquaresOver n f ≤ sumOver n fun _ => m * m :=
    sumOver_le_sumOver _ _ _ fun k hk => square_le_square _ _ (h k hk)
  rw [sumOver_const] at first
  have second := Int.mul_le_mul_of_nonneg_right root.2 (square_nonneg m)
  have e : m * rootUp n * (m * rootUp n) = rootUp n * rootUp n * (m * m) := by grind
  omega

/-- For `k ≥ 1`, `2^k` is twice `2^(k - 1)`. -/
theorem two_pow_split (k : Nat) (h : 1 ≤ k) : (2 : Int) ^ k = 2 * 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [Int.pow_succ, Int.mul_comm]

/-- What rounding adds: `2^shift * roundShift a shift` differs from `a` by at most `2^(shift - 1)`.
-/
theorem roundShift_error (a : Int) (shift : Nat) (positive : 1 ≤ shift) :
    magnitude (2 ^ shift * roundShift a shift - a) ≤ 2 ^ (shift - 1) := by
  have spec := roundShift_spec a shift
  have split := two_pow_split shift positive
  rw [Int.mul_comm (2 ^ shift) _, magnitude_le_iff]
  generalize roundShift a shift = r at *
  rw [Int.add_mul, Int.one_mul] at spec
  generalize r * 2 ^ shift = q at *
  omega

/-- **Rounding.** After `roundShift` with a shift of at least 1, a vector of `n` entries that was at
most `X` long is at most `roundedLength n X shift` long. -/
theorem length_roundShift {n : Nat} {f : Nat → Int} {X : Int} (h : LengthWithin n f X) (shift : Nat)
    (positive : 1 ≤ shift) :
    LengthWithin n (fun k => roundShift (f k) shift) (roundedLength n X shift) := by
  have pos : (0 : Int) < 2 ^ shift := Int.pow_pos (by decide)
  have half : (0 : Int) < 2 ^ (shift - 1) := Int.pow_pos (by decide)
  have error : LengthWithin n (fun k => 2 ^ shift * roundShift (f k) shift - f k)
      (2 ^ (shift - 1) * rootUp n) :=
    length_of_bound (fun k _ => roundShift_error (f k) shift positive) (by omega)
  have sum := length_add h error
  have same : (fun k => f k + (2 ^ shift * roundShift (f k) shift - f k)) =
      fun k => 2 ^ shift * roundShift (f k) shift := by
    funext k
    omega
  rw [same] at sum
  unfold roundedLength
  exact length_unscale pos (shiftUp_nonneg sum.1 shift) (length_of_le sum (shiftUp_spec _ _))

end IntegerTransformer.Bounds
