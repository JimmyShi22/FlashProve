-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/DualColumnBound.lean

A bound on a sum of products `sum a[k] u[k]` for a vector `a` that lies in a box and in a ball at
once. Pure arithmetic on `sumOver`; no model.
- `cappedSquare tau entry`: `entry^2` for `|entry| ≤ tau`, and the tangent line
  `2 tau |entry| - tau^2` beyond.
- `dual_coordinate`: for `tau > 0` and `|t| ≤ bound`,
  `2 tau bound t u ≤ tau^2 t^2 + bound^2 cappedSquare tau u`.
- `magnitude_inner_le_dual`: for `|a[k]| ≤ bound` with `bound > 0`, `a` at most `X` long and any
  whole number `tau > 0`, the sum is in absolute value at most
  `(tau^2 X^2 + bound^2 sum cappedSquare tau u[k]) / (2 tau bound)`, rounded down.
This is weak duality for the largest value of the sum over the box and the ball: every `tau` gives a
bound, and which `tau` gives the least depends on `u`.
Limits: nothing is said on how near a bound is to the largest value of the sum. The file imports
Lean's core and the model's own files.
-/
import IntegerModel.Bounds.LengthNeverFails

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-- The sum of two sequences, term by term. -/
theorem sumOver_add (n : Nat) (f g : Nat → Int) :
    sumOver n (fun k => f k + g k) = sumOver n f + sumOver n g := by
  induction n with
  | zero => simp [sumOver]
  | succ n ih =>
    simp only [sumOver, ih]
    omega

/-- `entry^2` for `|entry| ≤ tau`, and the tangent line `2 tau |entry| - tau^2` beyond. -/
def cappedSquare (tau entry : Int) : Int :=
  if magnitude entry ≤ tau then entry * entry else 2 * tau * magnitude entry - tau * tau

/-- One coordinate. -/
theorem dual_coordinate (tau bound u t : Int) (positive : 0 < tau) (box : magnitude t ≤ bound) :
    2 * tau * bound * (t * u) ≤ tau * tau * (t * t) + bound * bound * cappedSquare tau u := by
  unfold cappedSquare
  split
  · have square := square_nonneg (tau * t - bound * u)
    have e : (tau * t - bound * u) * (tau * t - bound * u) =
        tau * tau * (t * t) + bound * bound * (u * u) - 2 * tau * bound * (t * u) := by grind
    omega
  · next beyond =>
    have tNonneg := magnitude_nonneg t
    have product : t * u ≤ magnitude t * magnitude u := by
      rw [← magnitude_mul]; unfold magnitude; omega
    have squares := magnitude_mul_self t
    generalize magnitude t = r at *
    generalize magnitude u = p at *
    have scale : 0 ≤ 2 * tau * bound := Int.mul_nonneg (by omega) (by omega)
    have first := Int.mul_le_mul_of_nonneg_left product scale
    have h1 : tau * bound * tau ≤ tau * bound * p :=
      Int.mul_le_mul_of_nonneg_left (by omega) (Int.mul_nonneg (by omega) (by omega))
    have h2 : tau * tau * (bound + r) ≤ tau * tau * (2 * bound) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (Int.mul_nonneg (by omega) (by omega))
    have factor : 0 ≤ 2 * (tau * bound * p) - tau * tau * (bound + r) := by
      have e : tau * tau * (2 * bound) = 2 * (tau * bound * tau) := by grind
      omega
    have both := Int.mul_nonneg (by omega : 0 ≤ bound - r) factor
    have e : (bound - r) * (2 * (tau * bound * p) - tau * tau * (bound + r)) =
        tau * tau * (r * r) + bound * bound * (2 * tau * p - tau * tau)
          - 2 * tau * bound * (r * p) := by grind
    rw [← squares]
    omega

/-- The bound on a sum of products from the ball and the box together, for one `tau > 0`. -/
theorem magnitude_inner_le_dual {n : Nat} {a : Nat → Int} {X bound tau : Int} (u : Nat → Int)
    (box : ∀ k, k < n → magnitude (a k) ≤ bound) (ball : LengthWithin n a X) (positive : 0 < tau)
    (boundPositive : 0 < bound) :
    magnitude (sumOver n fun k => a k * u k) ≤
      (tau * tau * (X * X) + bound * bound * sumOver n fun k => cappedSquare tau (u k))
        / (2 * tau * bound) := by
  have divisor : 0 < 2 * tau * bound := Int.mul_pos (by omega) boundPositive
  have oneSide : ∀ b : Nat → Int, (∀ k, k < n → magnitude (b k) ≤ bound) →
      sumSquaresOver n b ≤ X * X →
      2 * tau * bound * (sumOver n fun k => b k * u k) ≤
        tau * tau * (X * X) + bound * bound * sumOver n fun k => cappedSquare tau (u k) := by
    intro b boxB ballB
    have terms := sumOver_le_sumOver n (fun k => 2 * tau * bound * (b k * u k))
      (fun k => tau * tau * (b k * b k) + bound * bound * cappedSquare tau (u k))
      fun k hk => dual_coordinate tau bound (u k) (b k) positive (boxB k hk)
    rw [sumOver_mul_left, sumOver_add, sumOver_mul_left, sumOver_mul_left] at terms
    have scaled := Int.mul_le_mul_of_nonneg_left ballB (square_nonneg tau)
    unfold sumSquaresOver at scaled
    omega
  have up := oneSide a box ball.2
  have down := oneSide (fun k => -a k) (fun k hk => by
    have := box k hk
    show magnitude (-a k) ≤ bound
    unfold magnitude at *
    omega) (by
    have same : sumSquaresOver n (fun k => -a k) = sumSquaresOver n a := by
      unfold sumSquaresOver
      simp only [Int.neg_mul_neg]
    rw [same]; exact ball.2)
  have negated : (sumOver n fun k => -a k * u k) = -(sumOver n fun k => a k * u k) := by
    have := sumOver_mul_left n (-1) fun k => a k * u k
    simp only [Int.neg_mul, Int.one_mul] at this ⊢
    exact this
  rw [negated] at down
  generalize (sumOver n fun k => a k * u k) = v at *
  generalize tau * tau * (X * X) + bound * bound * (sumOver n fun k => cappedSquare tau (u k)) = N
    at *
  rw [magnitude_le_iff]
  constructor
  · have : -v ≤ N / (2 * tau * bound) := by
      apply (Int.le_ediv_iff_mul_le divisor).mpr
      rw [Int.mul_comm]
      exact down
    omega
  · apply (Int.le_ediv_iff_mul_le divisor).mpr
    rw [Int.mul_comm]
    exact up

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.dual_coordinate
#print axioms IntegerTransformer.Bounds.magnitude_inner_le_dual
