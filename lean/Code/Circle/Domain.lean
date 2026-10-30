-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Circle/Domain.lean: the domain of a circle code.

The points are z_I = ζ^(2I+1), where ζ has the order 2n. Parts 1 and 2 hold over any field, Part 3
over any commutative ring.

 * Part 1: an odd power of an element of order 2^(L+1) does not become 1 when it is squared at most
   L times (`pow_pow_ne_one`).
 * Part 2: for ζ of order 2n, n = 2^L ≥ 2, the points z_I, I < n, are distinct and none of them is
   (-1, 0) (`circlePoints_points`); π_j has no zero among them for j < L, and bas_i none for i < n
   (`pi_points_ne_zero`, `bas_points_ne_zero`).
 * Part 3: on the circle, z^(2^k) is the result of squaring k times on pairs (`pow_two_pow`), and
   the point (-1, 0) has the square 1 (`negOne_sq`).

One further fact that belongs with these (on the circle group, the points or the functions π_j and
bas_i) is not shown.
-/
import Mathlib.GroupTheory.OrderOfElement
import Code.Circle.Basis
import Code.Field

set_option autoImplicit false

namespace Code.Circle

/-! ## Part 1. Orders -/

/-- An odd power of an element of order 2^(L+1) does not become 1 when it is squared at most L
times. -/
theorem pow_pow_ne_one {G : Type*} [Monoid G] {ζ : G} {L : ℕ} (hζ : orderOf ζ = 2 ^ (L + 1)) {e : ℕ}
    (he : e % 2 = 1) {m : ℕ} (hm : m ≤ L) : (ζ ^ e) ^ 2 ^ m ≠ 1 := by
  intro h
  rw [← pow_mul] at h
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hζ] at hdvd
  have hsplit : 2 ^ (L + 1) = 2 ^ (L + 1 - m) * 2 ^ m := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at hdvd
  have hd2 : 2 ^ (L + 1 - m) ∣ e := Nat.dvd_of_mul_dvd_mul_right (by positivity) hdvd
  have h2 : 2 ∣ e := dvd_trans (dvd_pow_self 2 (by omega)) hd2
  omega

/-! ## Part 2. The points -/

/-- The points of the code: z_I = ζ^(2I+1) for I < n. -/
def points {R : Type*} [CommRing R] (ζ : Circ R) (n : ℕ) : Fin n → Circ R := fun I =>
  ζ ^ (2 * (I : ℕ) + 1)

section Points

variable {K : Type*} [Field K] {ζ : Circ K} {L : ℕ}

theorem points_pow_ne_one (hζ : orderOf ζ = 2 ^ (L + 1)) {n : ℕ} (I : Fin n) {m : ℕ} (hm : m ≤ L) :
    points ζ n I ^ 2 ^ m ≠ 1 :=
  pow_pow_ne_one hζ (by omega) hm

/-- If ζ has the order 2n with n = 2^L ≥ 2, the n points z_I are distinct, and none of them is (-1,
0). -/
theorem circlePoints_points (hL : 1 ≤ L) (hζ : orderOf ζ = 2 ^ (L + 1)) :
    CirclePoints (points ζ (2 ^ L)) where
  ne I h0 := by
    have hx : (points ζ (2 ^ L) I).x = -1 := by linear_combination h0
    have hy2 : (points ζ (2 ^ L) I).y ^ 2 = 0 := by
      have hon := (points ζ (2 ^ L) I).on
      rw [hx] at hon
      linear_combination hon
    have hy : (points ζ (2 ^ L) I).y = 0 := (pow_eq_zero_iff two_ne_zero).1 hy2
    refine points_pow_ne_one hζ I hL ?_
    rw [pow_one]
    exact Circ.sq_eq_one_of_y _ hy
  inj I I' h := by
    have h1 : ζ ^ (2 * (I : ℕ) + 1) = ζ ^ (2 * (I' : ℕ) + 1) := h
    have hI := I.2
    have hI' := I'.2
    have hp : 2 ^ (L + 1) = 2 ^ L * 2 := pow_succ 2 L
    rw [pow_inj_mod, hζ, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    exact Fin.ext (by omega)

/-- Under `hζ`, for j < L, π_j has no zero among the points. -/
theorem pi_points_ne_zero (hζ : orderOf ζ = 2 ^ (L + 1)) {n : ℕ} (I : Fin n) {j : ℕ} (hj : j < L) :
    pi j (points ζ n I) ≠ 0 := by
  intro h0
  cases j with
  | zero =>
    refine points_pow_ne_one hζ I (m := 1) (by omega) ?_
    rw [pow_one]
    exact Circ.sq_eq_one_of_y _ h0
  | succ k =>
    have hx : (points ζ n I ^ 2 ^ k).x = 0 := h0
    refine points_pow_ne_one hζ I (m := k + 2) (by omega) ?_
    have h4 := Circ.sq_eq_one_of_y _ (Circ.sq_y_of_x _ hx)
    rw [← pow_mul, ← pow_mul] at h4
    rw [pow_succ, pow_succ, mul_assoc]
    exact h4

/-- Under `hζ`, for i < 2^L, bas_i has no zero among the points. -/
theorem bas_points_ne_zero (hζ : orderOf ζ = 2 ^ (L + 1)) {n : ℕ} (I : Fin n)
    {i : ℕ} (hi : i < 2 ^ L) : bas i (points ζ n I) ≠ 0 := by
  rw [bas_eq_prod hi, Finset.prod_ne_zero_iff]
  intro j hj
  split_ifs
  · exact pi_points_ne_zero hζ I (Finset.mem_range.1 hj)
  · exact one_ne_zero

end Points

/-! ## Part 3. Squaring on the circle, and the point (-1, 0) -/

/-- Squaring in the circle group, on pairs. -/
def sqPair {R : Type*} [CommRing R] (w : R × R) : R × R :=
  (w.1 * w.1 - w.2 * w.2, w.1 * w.2 + w.2 * w.1)

/-- The power z^(2^k) is the result of squaring k times. -/
theorem pow_two_pow {R : Type*} [CommRing R] (z : Circ R) (k : ℕ) :
    ((z ^ 2 ^ k).x, (z ^ 2 ^ k).y) = sqPair^[k] (z.x, z.y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, Function.iterate_succ_apply', ← ih, pow_two]
    rfl

/-- The point (-1, 0); its square is 1 (`negOne_sq`). -/
def negOne (R : Type*) [CommRing R] : Circ R := ⟨-1, 0, by ring⟩

theorem negOne_sq (R : Type*) [CommRing R] : negOne R ^ 2 = 1 := Circ.sq_eq_one_of_y _ rfl

end Code.Circle
