-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/ReadPoly.lean: lists of the program's field elements, read in a field: a
list of coefficients as a polynomial; a list applied to a row of values; the powers of an element.
Small tools for OnBytes/Desc/First/P1/PscSound.lean. Definitions, statements and proofs.

  `polyOf` with `polyOf_eval` (its value is the reading of the program's `polyAt`), `polyOf_coeff`,
    `polyOf_natDegree_lt`.
  `dotFrom` with `dotFrom_append`, `dotFrom_congr` (it reads the row at the list's places alone).
  `powersFrom` (a, a x, a x^2, ...) with `powersFrom_length`, `dotFrom_powers`. `eval_polyFrom`.


-/
import OnBytes.Desc.First.P1.SumCore
import OnBytes.Model.HideLaws
import OnBytes.Iop.Psc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model Polynomial

variable {K : Type} [Field K] (ρ : Reading K)

/-- A list of coefficients, lowest first, as a polynomial. -/
def polyOf : List E → K[X]
  | [] => 0
  | c :: g => C (ρ.val c) + X * polyOf g

theorem polyOf_eval (x : E) : ∀ g : List E,
    (polyOf ρ g).eval (ρ.val x) = ρ.val (OnBytes.Psc.polyAt g x)
  | [] => by simp [polyOf, OnBytes.Psc.polyAt, ρ.zero]
  | c :: g => by
    have hv : OnBytes.Psc.polyAt (c :: g) x = addE (mulE (OnBytes.Psc.polyAt g x) x) c := rfl
    rw [hv, ρ.add, ρ.mul, polyOf, eval_add, eval_C, eval_mul, eval_X, polyOf_eval x g]
    ring

theorem polyOf_coeff : ∀ (g : List E) (i : ℕ), (polyOf ρ g).coeff i = ρ.val (g.getD i zeroE)
  | [], i => by simp [polyOf, ρ.zero]
  | c :: g, 0 => by simp [polyOf]
  | c :: g, i + 1 => by
    rw [polyOf, coeff_add, coeff_C_succ, coeff_X_mul, polyOf_coeff g i]
    simp

theorem polyOf_natDegree_lt (g : List E) (h : 0 < g.length) :
    (polyOf ρ g).natDegree < g.length := by
  have hle : (polyOf ρ g).natDegree ≤ g.length - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [polyOf_coeff]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show g.length ≤ N by omega), ρ.zero]
  omega

/-- a, a x, a x^2, ...: n members. -/
def powersFrom (x : E) : Nat → E → List E
  | 0, _ => []
  | n + 1, a => a :: powersFrom x n (mulE a x)

/-- The list u applied to the values h 0, h 1, ... -/
def dotFrom (h : ℕ → K) : List E → K
  | [] => 0
  | x :: u => ρ.val x * h 0 + dotFrom (fun i => h (i + 1)) u

theorem dotFrom_append : ∀ (a b : List E) (h : ℕ → K),
    dotFrom ρ h (a ++ b) = dotFrom ρ h a + dotFrom ρ (fun i => h (a.length + i)) b
  | [], b, h => by simp [dotFrom]
  | x :: a, b, h => by
    have hf : (fun i => h (a.length + i + 1)) = fun i => h ((x :: a).length + i) := by
      funext i
      congr 1
      show a.length + i + 1 = a.length + 1 + i
      omega
    rw [List.cons_append, dotFrom, dotFrom, dotFrom_append a b, add_assoc, hf]

/-- It reads h at the list's places alone. -/
theorem dotFrom_congr : ∀ (u : List E) (h h' : ℕ → K), (∀ i, i < u.length → h i = h' i) →
    dotFrom ρ h u = dotFrom ρ h' u
  | [], _, _, _ => rfl
  | x :: u, h, h', H => by
    rw [dotFrom, dotFrom, H 0 (by simp),
      dotFrom_congr u (fun i => h (i + 1)) (fun i => h' (i + 1)) fun i hi =>
        H (i + 1) (by simpa using hi)]

theorem powersFrom_length (r : E) : ∀ (n : ℕ) (a : E), (powersFrom r n a).length = n
  | 0, _ => rfl
  | n + 1, a => by rw [powersFrom, List.length_cons, powersFrom_length r n]

theorem dotFrom_powers (r : E) : ∀ (n : ℕ) (a : E) (h : ℕ → K),
    dotFrom ρ h (powersFrom r n a) = ρ.val a * ∑ i ∈ Finset.range n, h i * ρ.val r ^ i
  | 0, _, _ => by simp [powersFrom, dotFrom]
  | n + 1, a, h => by
    rw [powersFrom, dotFrom, dotFrom_powers r n, Finset.sum_range_succ', ρ.mul, Finset.mul_sum,
      mul_add, Finset.mul_sum, pow_zero, mul_one, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

theorem eval_polyFrom (h : ℕ → K) (s n : ℕ) (x : K) :
    (polyFrom h s n).eval x = ∑ i ∈ Finset.range n, h i * x ^ (s + i) := by
  simp [polyFrom, eval_finset_sum]

end OnBytes.Desc.First.P1
