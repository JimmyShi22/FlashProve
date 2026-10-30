-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Tie/Point.lean: the evaluation point of a position x in a Reed-Solomon code of
length 2^a (Fmt.M1.point a x, Fmt/M1Codes.lean) depends only on x modulo 2^a.
Terms: Johnson/SendSim/Defs.lean, "Terms of the model". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves, for all a, x and y, about the library's executable definition of the point.
  point_mod         point a (x % 2^a) = point a x.
  point_eq_of_mod   If x % 2^a = y % 2^a, then point a x = point a y.
  toF_point_eq_iff  For a ≤ 32: the points of x and y are equal as elements of the base field (toF)
                    if and only if x % 2^a = y % 2^a.
  pointFrom_congr   The loop pointFrom x n i acc depends only on the bits i to i + n - 1 of x.

Limits. For a above 32, toF_point_eq_iff states nothing: the points are 7 times powers of a root of
unity of order 2^32 (OnBytes/Slice/Points.lean). That a code of the release has a ≤ 32 is not stated
here.

How it fits. point_mod serves rowsExact (Johnson/SendSim/At/RowsExact.lean) and rowsFresh
(Johnson/SendSim/At/RowsFresh.lean): by it withinOf (Johnson/SendSim/At/Within.lean) derives the
general model's bound on points (Within) from the bound on queried positions (budAt), which counts
positions modulo 2^a. toF_point_eq_iff rests on toF_point_inj (OnBytes/Slice/Points.lean), which is
about positions below 2^a.
-/
import OnBytes.Slice.Points

set_option autoImplicit false

namespace OnBytes.SendSim
open OnBytes.Slice

/-- If x and y have the same bits i, ..., i + n - 1, then the loop pointFrom gives the same value at
x and at y, for every starting value acc. -/
theorem pointFrom_congr (x y : ℕ) : ∀ (n i : ℕ) (acc : UInt64),
    (∀ j, i ≤ j → j < i + n → x.testBit j = y.testBit j) →
    Fmt.M1.pointFrom x n i acc = Fmt.M1.pointFrom y n i acc
  | 0, _, _, _ => rfl
  | n + 1, i, acc, h => by
    show Fmt.M1.pointFrom x n (i + 1) _ = Fmt.M1.pointFrom y n (i + 1) _
    rw [h i (Nat.le_refl i) (by omega)]
    exact pointFrom_congr x y n (i + 1) _ fun j h1 h2 => h j (by omega) (by omega)

/-- The point of a position x in a code of length 2^a is the point of x % 2^a. -/
theorem point_mod (a x : ℕ) : Fmt.M1.point a (x % 2 ^ a) = Fmt.M1.point a x :=
  pointFrom_congr _ _ a 0 7 fun j _ h2 => by
    rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega : j < a), Bool.true_and]

/-- Two positions that are equal modulo 2^a have the same point. -/
theorem point_eq_of_mod (a : ℕ) {x y : ℕ} (h : x % 2 ^ a = y % 2 ^ a) :
    Fmt.M1.point a x = Fmt.M1.point a y := by
  rw [← point_mod a x, ← point_mod a y, h]

/-- For a ≤ 32, two positions have the same point in the base field if and only if they are equal
modulo 2^a. -/
theorem toF_point_eq_iff (a : ℕ) (ha : a ≤ 32) (x y : ℕ) :
    toF (Fmt.M1.point a x) = toF (Fmt.M1.point a y) ↔ x % 2 ^ a = y % 2 ^ a := by
  constructor
  · intro h
    rw [← point_mod a x, ← point_mod a y] at h
    exact toF_point_inj a ha (Nat.mod_lt _ (Nat.two_pow_pos a)) (Nat.mod_lt _ (Nat.two_pow_pos a)) h
  · intro h
    rw [point_eq_of_mod a h]

end OnBytes.SendSim

#print axioms OnBytes.SendSim.point_mod
#print axioms OnBytes.SendSim.toF_point_eq_iff
