-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Circle/Basis.lean: the circle group, the functions π_j and bas_i, and the projection to a line.

Parts 1 and 2: any commutative ring. Part 3: any field, mostly with 2 ≠ 0 (`h2`).

 * Part 1: the group `Circ R` of the points of x^2 + y^2 = 1, and its functoriality `Circ.map`.
 * Part 2: `pi j z` with the recursion π_(j+1) = 2 π_j^2 - 1 for j ≥ 1, `bas i z`, and `bas_add`.
 * Part 3: the projection `theta z`, the conditions `CirclePoints` on a family of points, and
   `bas_eq_basis`: under its hypotheses, bas_i at z is the function `basis B i` of
   Code/Circle/Poly.lean at theta z.

Notation:
  `xAt t`, `yAt t` (Code/Circle/Poly.lean): elements of the field: the first coordinate x and the
    second coordinate y of the point with the projection `t`;
  `Xs i t` (Code/Circle/Poly.lean): an element of the field: `Xs 0 = x` and
    `Xs (i + 1) = 2 (Xs i)^2 - 1`;
  `basis B j t` (Code/Circle/Poly.lean), for natural numbers B, j: an element of the field: basis
    function `j`, for `j < 2^(B+1)`: the factor y if binary digit 0 of `j` is 1, times `Xs i` for
    each `i < B` such that binary digit `i + 1` of `j` is 1.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Code.Circle.Poly

set_option autoImplicit false

namespace Code.Circle

/-! ## Part 1. The circle group -/

/-- The circle group U = {(x, y) : x² + y² = 1} over a commutative ring, with the product
(x, y)(x', y') = (x x' - y y', x y' + y x'). -/
@[ext] structure Circ (R : Type*) [CommRing R] where
  x : R
  y : R
  on : x ^ 2 + y ^ 2 = 1

namespace Circ

variable {R S : Type*} [CommRing R] [CommRing S]

instance : Mul (Circ R) := ⟨fun z w => ⟨z.x * w.x - z.y * w.y, z.x * w.y + z.y * w.x, by
  linear_combination (w.x ^ 2 + w.y ^ 2) * z.on + w.on⟩⟩
instance : One (Circ R) := ⟨⟨1, 0, by ring⟩⟩
instance : Inv (Circ R) := ⟨fun z => ⟨z.x, -z.y, by linear_combination z.on⟩⟩

@[simp] theorem mul_x (z w : Circ R) : (z * w).x = z.x * w.x - z.y * w.y := rfl
@[simp] theorem mul_y (z w : Circ R) : (z * w).y = z.x * w.y + z.y * w.x := rfl
@[simp] theorem one_x : (1 : Circ R).x = 1 := rfl
@[simp] theorem one_y : (1 : Circ R).y = 0 := rfl
@[simp] theorem inv_x (z : Circ R) : z⁻¹.x = z.x := rfl
@[simp] theorem inv_y (z : Circ R) : z⁻¹.y = -z.y := rfl

instance : CommGroup (Circ R) where
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by
    ext
    · simp only [mul_x, inv_x, inv_y, one_x]; linear_combination a.on
    · simp only [mul_y, inv_x, inv_y, one_y]; ring
  mul_comm a b := by ext <;> simp <;> ring

/-- The first coordinate of a square is 2 x² - 1. -/
theorem sq_x (w : Circ R) : (w ^ 2).x = 2 * w.x ^ 2 - 1 := by
  rw [pow_two, mul_x]
  linear_combination (-1 : R) * w.on

/-- A point with y = 0 has the square 1. -/
theorem sq_eq_one_of_y (w : Circ R) (h : w.y = 0) : w ^ 2 = 1 := by
  rw [pow_two]
  ext
  · simp only [mul_x, one_x]
    linear_combination w.on - 2 * w.y * h
  · simp only [mul_y, one_y]
    linear_combination 2 * w.x * h

/-- The square of a point with x = 0 has y = 0. -/
theorem sq_y_of_x (w : Circ R) (h : w.x = 0) : (w ^ 2).y = 0 := by
  rw [pow_two, mul_y]
  linear_combination 2 * w.y * h

/-- A ring homomorphism acts on the points of the circle, and this is a homomorphism of groups. -/
def map (f : R →+* S) : Circ R →* Circ S where
  toFun z := ⟨f z.x, f z.y, by rw [← map_pow, ← map_pow, ← map_add, z.on, map_one]⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

@[simp] theorem map_x (f : R →+* S) (z : Circ R) : (map f z).x = f z.x := rfl
@[simp] theorem map_y (f : R →+* S) (z : Circ R) : (map f z).y = f z.y := rfl

theorem map_injective {f : R →+* S} (hf : Function.Injective f) : Function.Injective (map f) :=
  fun _ _ h => Circ.ext (hf (congrArg Circ.x h)) (hf (congrArg Circ.y h))

end Circ

/-! ## Part 2. The functions π_j and bas_i -/

section Bas

variable {R S : Type*} [CommRing R] [CommRing S]

/-- π_0(z) = y, and for j ≥ 1, π_j(z) is the first coordinate of z^(2^(j-1)). -/
def pi : ℕ → Circ R → R
  | 0, z => z.y
  | j + 1, z => (z ^ 2 ^ j).x

theorem pi_zero (z : Circ R) : pi 0 z = z.y := rfl

theorem pi_one (z : Circ R) : pi 1 z = z.x := by
  show (z ^ 2 ^ 0).x = z.x
  rw [pow_zero, pow_one]

/-- π_(j+1) = 2 π_j² - 1 for j ≥ 1. -/
theorem pi_succ_succ (j : ℕ) (z : Circ R) : pi (j + 2) z = 2 * pi (j + 1) z ^ 2 - 1 := by
  show (z ^ 2 ^ (j + 1)).x = 2 * (z ^ 2 ^ j).x ^ 2 - 1
  rw [pow_succ, pow_mul, Circ.sq_x]

theorem pi_map (f : R →+* S) (j : ℕ) (z : Circ R) : pi j (Circ.map f z) = f (pi j z) := by
  cases j with
  | zero => rfl
  | succ j =>
    show ((Circ.map f z) ^ 2 ^ j).x = f (z ^ 2 ^ j).x
    rw [← map_pow]
    rfl

/-- bas_i is the product of the π_j over the indices j of the one-bits of i; the lowest bit has
index 0. -/
def bas (i : ℕ) (z : Circ R) : R := ∏ j ∈ Finset.range i.size, if i.testBit j then pi j z else 1

/-- For i < 2^L the product may be taken over the indices below L. -/
theorem bas_eq_prod {L i : ℕ} (h : i < 2 ^ L) (z : Circ R) :
    bas i z = ∏ j ∈ Finset.range L, if i.testBit j then pi j z else 1 := by
  unfold bas
  refine Finset.prod_subset (Finset.range_subset_range.2 (Nat.size_le.2 h)) fun j _ hj => ?_
  have hj' : i.size ≤ j := by simpa using hj
  rw [Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (Nat.lt_size_self i) (Nat.pow_le_pow_right (by norm_num) hj'))]
  simp

theorem bas_zero (z : Circ R) : bas 0 z = 1 := by simp [bas]

theorem bas_map (f : R →+* S) (i : ℕ) (z : Circ R) : bas i (Circ.map f z) = f (bas i z) := by
  unfold bas
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · exact pi_map f j z
  · rw [map_one]

/-- If 2^s divides i0 and i' < 2^s, no binary digit is set in both, and bas_(i0 + i') = bas_(i0)
bas_(i'). -/
theorem bas_add {s i0 i' : ℕ} (hd : 2 ^ s ∣ i0) (hi : i' < 2 ^ s) (z : Circ R) :
    bas (i0 + i') z = bas i0 z * bas i' z := by
  have hL : i0 + i' < 2 ^ (i0 + i') := Nat.lt_two_pow_self
  rw [bas_eq_prod hL, bas_eq_prod (lt_of_le_of_lt (Nat.le_add_right i0 i') hL),
    bas_eq_prod (lt_of_le_of_lt (Nat.le_add_left i' i0) hL)]
  obtain ⟨k, rfl⟩ := hd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Nat.testBit_two_pow_mul_add k hi j, Nat.testBit_two_pow_mul]
  by_cases hj : j < s
  · have hj' : ¬ s ≤ j := by omega
    simp [hj, hj']
  · have hj' : s ≤ j := by omega
    have hb : i'.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hj'))
    simp [hj, hj', hb]

end Bas

/-! ## Part 3. The projection to a line -/

section Theta

variable {K : Type*} [Field K]

/-- The projection of a point of the circle from (-1, 0): θ = y / (1 + x). -/
def theta (z : Circ K) : K := z.y / (1 + z.x)

/-- The conditions on the points of a code: they are distinct, and none of them is (-1, 0). -/
structure CirclePoints {P : Type*} (z : P → Circ K) : Prop where
  ne : ∀ I, 1 + (z I).x ≠ 0
  inj : Function.Injective z

/-- If 2 ≠ 0 and z is not (-1, 0) (`h2`, `hne`), then 1 + θ² is not 0. -/
theorem den_ne (h2 : (2 : K) ≠ 0) (z : Circ K) (hne : 1 + z.x ≠ 0) : 1 + theta z ^ 2 ≠ 0 :=
  (proj h2 z.x z.y z.on hne).1

theorem xAt_theta (h2 : (2 : K) ≠ 0) (z : Circ K) (hne : 1 + z.x ≠ 0) : xAt (theta z) = z.x :=
  (proj h2 z.x z.y z.on hne).2.1

theorem yAt_theta (h2 : (2 : K) ≠ 0) (z : Circ K) (hne : 1 + z.x ≠ 0) : yAt (theta z) = z.y :=
  (proj h2 z.x z.y z.on hne).2.2

/-- Under `hz`, `h2`: the projections of distinct points are distinct. -/
theorem CirclePoints.theta_injective
    {P : Type*} {z : P → Circ K} (hz : CirclePoints z) (h2 : (2 : K) ≠ 0) :
    Function.Injective fun I => theta (z I) := by
  intro I I' h
  have h' : theta (z I) = theta (z I') := h
  apply hz.inj
  ext
  · rw [← xAt_theta h2 _ (hz.ne I), ← xAt_theta h2 _ (hz.ne I'), h']
  · rw [← yAt_theta h2 _ (hz.ne I), ← yAt_theta h2 _ (hz.ne I'), h']

/-- `CirclePoints` carries over to an extension field. -/
theorem CirclePoints.map {P : Type*} {z : P → Circ K} (hz : CirclePoints z) {K' : Type*}
    [Field K'] (f : K →+* K') :
    CirclePoints fun I => Circ.map f (z I) where
  ne I h := hz.ne I (f.injective (by rw [map_add, map_one, map_zero]; exact h))
  inj I I' h := hz.inj (Circ.map_injective f.injective h)

/-- Under `h2`, `hne`: π_(i+1) at z is the function `Xs i` at the projection of z. -/
theorem Xs_theta (h2 : (2 : K) ≠ 0) (z : Circ K) (hne : 1 + z.x ≠ 0) :
    ∀ i : ℕ, Xs i (theta z) = pi (i + 1) z
  | 0 => by rw [pi_one]; exact xAt_theta h2 z hne
  | i + 1 => by
    rw [pi_succ_succ, ← Xs_theta h2 z hne i]
    rfl

/-- Under `h2`, at a point z other than (-1, 0), bas_i is the function `basis B i` at the
projection of z, for i < 2^(B+1). -/
theorem bas_eq_basis (h2 : (2 : K) ≠ 0) {B i : ℕ} (hi : i < 2 ^ (B + 1))
    (z : Circ K) (hne : 1 + z.x ≠ 0) :
    bas i z = basis B i (theta z) := by
  rw [bas_eq_prod hi, Finset.prod_range_succ', mul_comm]
  unfold basis
  congr 1
  · rw [yAt_theta h2 z hne]
    rfl
  · exact Finset.prod_congr rfl fun j _ => by rw [Xs_theta h2 z hne j]

end Theta

end Code.Circle
