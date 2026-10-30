-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Poly.lean: the list functions of Johnson/Desc/K5/Honest/Terms.lean
(`addP`, `scaleP`, `mulP`, `lineP`, `sumP`), which compute in the program's type, READ IN A FIELD:
as polynomials (`polyOf`, Johnson/Desc/Part/MaskedSumSound.lean), by their values at a point
(`valueAt`, Johnson/Desc/Part/MaskedSum4.lean), and their lengths. Statements with their proofs.
rho: any reading (OnBytes/Model/HideLaws.lean). No word is asked to be below the prime.

Main names:
  `polyOf_addP`, `polyOf_scaleP`, `polyOf_mulP`, `polyOf_lineP`, `polyOf_sumP`, `polyOf_pair`
        each list as a polynomial
  `read_valueAt`   the value of a list at a point is the polynomial's
  `value_addP`, `value_scaleP`, `value_mulP`, `value_lineP`, `value_sumP`, `value_pair`,
  `value_single`   the values at a point; a line's value at r is (1 - r) v0 + r v1
  `value_zero`     the value at 0 is the lowest coefficient
  `length_addP`, `length_scaleP`, `length_mulP_cons`, `length_mulP_pair`, `length_lineP`,
  `length_sumP_le`  lengths
  `read_beyond`    a member beyond a list's end reads 0

Limits. Equations on these functions alone, unconditional but for the stated lengths. Nothing on a
protocol. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Terms
import Johnson.Desc.Part.MaskedSumSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (polyOf polyOf_eval polyOf_coeff valueAt)
open Polynomial

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## As polynomials -/

theorem polyOf_nil : polyOf ρ [] = 0 := rfl

theorem polyOf_cons (c : E) (g : List E) : polyOf ρ (c :: g) = C (ρ.val c) + X * polyOf ρ g := rfl

theorem polyOf_addP : ∀ a b : List E, polyOf ρ (addP a b) = polyOf ρ a + polyOf ρ b
  | [], b => by
    show polyOf ρ b = polyOf ρ [] + polyOf ρ b
    rw [polyOf_nil, zero_add]
  | x :: a, [] => by
    show polyOf ρ (x :: a) = polyOf ρ (x :: a) + polyOf ρ []
    rw [polyOf_nil, add_zero]
  | x :: a, y :: b => by
    show polyOf ρ (addE x y :: addP a b) = _
    rw [polyOf_cons, polyOf_cons, polyOf_cons, polyOf_addP a b, ρ.add, C_add]
    ring

theorem polyOf_scaleP (k : E) : ∀ a : List E, polyOf ρ (scaleP k a) = C (ρ.val k) * polyOf ρ a
  | [] => by
    show polyOf ρ [] = _
    rw [polyOf_nil, mul_zero]
  | x :: a => by
    show polyOf ρ (mulE k x :: scaleP k a) = _
    rw [polyOf_cons, polyOf_cons, polyOf_scaleP k a, ρ.mul, C_mul]
    ring

theorem polyOf_mulP : ∀ a b : List E, polyOf ρ (mulP a b) = polyOf ρ a * polyOf ρ b
  | [], b => by
    show polyOf ρ [] = _
    rw [polyOf_nil, zero_mul]
  | x :: a, b => by
    show polyOf ρ (addP (scaleP x b) (zeroE :: mulP a b)) = _
    rw [polyOf_addP, polyOf_scaleP, polyOf_cons, polyOf_cons, polyOf_mulP a b, ρ.zero, C_0]
    ring

/-- A list of two members. -/
theorem polyOf_pair (u s : E) : polyOf ρ [u, s] = C (ρ.val u) + X * C (ρ.val s) := by
  rw [polyOf_cons, polyOf_cons, polyOf_nil, mul_zero, add_zero]

theorem polyOf_lineP (v0 v1 : E) :
    polyOf ρ (lineP v0 v1) = C (ρ.val v0) + X * C (ρ.val v1 - ρ.val v0) := by
  show polyOf ρ [v0, subE v1 v0] = _
  rw [polyOf_pair, ρ.sub]

theorem polyOf_foldl_addP : ∀ (l : List (List E)) (a : List E),
    polyOf ρ (l.foldl addP a) = polyOf ρ a + (l.map (polyOf ρ)).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, polyOf_foldl_addP l, polyOf_addP, List.map_cons, List.sum_cons, add_assoc]

theorem polyOf_sumP (l : List (List E)) : polyOf ρ (sumP l) = (l.map (polyOf ρ)).sum := by
  unfold sumP
  rw [polyOf_foldl_addP, polyOf_nil, zero_add]

/-! ## Values at a point -/

/-- The value of a list at a point is the polynomial's. -/
theorem read_valueAt (g : List E) (x : E) : ρ.val (valueAt g x) = (polyOf ρ g).eval (ρ.val x) :=
  (polyOf_eval ρ x g).symm

theorem value_addP (a b : List E) (x : E) :
    ρ.val (valueAt (addP a b) x) = ρ.val (valueAt a x) + ρ.val (valueAt b x) := by
  rw [read_valueAt, read_valueAt, read_valueAt, polyOf_addP, eval_add]

theorem value_scaleP (k : E) (a : List E) (x : E) :
    ρ.val (valueAt (scaleP k a) x) = ρ.val k * ρ.val (valueAt a x) := by
  rw [read_valueAt, read_valueAt, polyOf_scaleP, eval_mul, eval_C]

theorem value_mulP (a b : List E) (x : E) :
    ρ.val (valueAt (mulP a b) x) = ρ.val (valueAt a x) * ρ.val (valueAt b x) := by
  rw [read_valueAt, read_valueAt, read_valueAt, polyOf_mulP, eval_mul]

theorem value_single (c x : E) : ρ.val (valueAt [c] x) = ρ.val c := by
  rw [read_valueAt, polyOf_cons, polyOf_nil, mul_zero, add_zero, eval_C]

theorem value_pair (u s x : E) : ρ.val (valueAt [u, s] x) = ρ.val u + ρ.val s * ρ.val x := by
  rw [read_valueAt, polyOf_pair, eval_add, eval_C, eval_mul, eval_X, eval_C, mul_comm]

/-- **A line's value at r** is (1 - r) times its value at 0 plus r times its value at 1. -/
theorem value_lineP (v0 v1 r : E) :
    ρ.val (valueAt (lineP v0 v1) r) = (1 - ρ.val r) * ρ.val v0 + ρ.val r * ρ.val v1 := by
  rw [read_valueAt, polyOf_lineP, eval_add, eval_C, eval_mul, eval_X, eval_C]
  ring

theorem value_sumP (l : List (List E)) (x : E) :
    ρ.val (valueAt (sumP l) x) = (l.map fun g => ρ.val (valueAt g x)).sum := by
  rw [read_valueAt, polyOf_sumP]
  induction l with
  | nil => simp
  | cons g l ih => rw [List.map_cons, List.sum_cons, eval_add, ih, List.map_cons, List.sum_cons,
      read_valueAt]

/-- The value at 0 is the lowest coefficient. -/
theorem value_zero (g : List E) : ρ.val (valueAt g zeroE) = ρ.val (g.getD 0 zeroE) := by
  rw [read_valueAt, ρ.zero, ← polyOf_coeff, coeff_zero_eq_eval_zero]

/-! ## Lengths -/

theorem length_addP : ∀ a b : List E, (addP a b).length = max a.length b.length
  | [], b => by
    show b.length = max 0 b.length
    rw [Nat.zero_max]
  | x :: a, [] => by
    show (x :: a).length = max (x :: a).length 0
    rw [Nat.max_zero]
  | x :: a, y :: b => by
    show (addE x y :: addP a b).length = _
    rw [List.length_cons, List.length_cons, List.length_cons, length_addP a b]
    omega

theorem length_scaleP (k : E) (a : List E) : (scaleP k a).length = a.length := by
  unfold scaleP
  rw [List.length_map]

/-- The product of two lists that are not empty has one member fewer than both together. -/
theorem length_mulP_cons (y : E) (b : List E) : ∀ (x : E) (a : List E),
    (mulP (x :: a) (y :: b)).length = a.length + b.length + 1
  | x, [] => by
    show (addP (scaleP x (y :: b)) [zeroE]).length = _
    rw [length_addP, length_scaleP]
    simp only [List.length_cons, List.length_nil]
    omega
  | x, x' :: a => by
    show (addP (scaleP x (y :: b)) (zeroE :: mulP (x' :: a) (y :: b))).length = _
    rw [length_addP, length_scaleP]
    simp only [List.length_cons]
    rw [length_mulP_cons y b x' a]
    omega

/-- A list that is not empty, times a list of two members, has one member more. -/
theorem length_mulP_pair (a : List E) (u s : E) (h : a ≠ []) :
    (mulP a [u, s]).length = a.length + 1 := by
  cases a with
  | nil => exact absurd rfl h
  | cons x a =>
    rw [length_mulP_cons]
    simp only [List.length_cons, List.length_nil]

theorem length_lineP (v0 v1 : E) : (lineP v0 v1).length = 2 := rfl

theorem length_foldl_addP_le (n : Nat) : ∀ (l : List (List E)) (a : List E), a.length ≤ n →
    (∀ g ∈ l, g.length ≤ n) → (l.foldl addP a).length ≤ n
  | [], _, ha, _ => ha
  | x :: l, a, ha, h => by
    rw [List.foldl_cons]
    refine length_foldl_addP_le n l _ ?_ fun g hg => h g (List.mem_cons_of_mem _ hg)
    rw [length_addP]
    exact Nat.max_le.2 ⟨ha, h x List.mem_cons_self⟩

/-- A sum of lists is not longer than the longest. -/
theorem length_sumP_le (n : Nat) (l : List (List E)) (h : ∀ g ∈ l, g.length ≤ n) :
    (sumP l).length ≤ n :=
  length_foldl_addP_le n l [] (Nat.zero_le n) h

/-- A member beyond a list's end reads 0. -/
theorem read_beyond (g : List E) (j : Nat) (h : g.length ≤ j) : ρ.val (g.getD j zeroE) = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  exact ρ.zero

end H2K5.Honest

#print axioms H2K5.Honest.polyOf_nil
#print axioms H2K5.Honest.polyOf_cons
#print axioms H2K5.Honest.polyOf_addP
#print axioms H2K5.Honest.polyOf_scaleP
#print axioms H2K5.Honest.polyOf_mulP
#print axioms H2K5.Honest.polyOf_pair
#print axioms H2K5.Honest.polyOf_lineP
#print axioms H2K5.Honest.polyOf_foldl_addP
#print axioms H2K5.Honest.polyOf_sumP
#print axioms H2K5.Honest.read_valueAt
#print axioms H2K5.Honest.value_addP
#print axioms H2K5.Honest.value_scaleP
#print axioms H2K5.Honest.value_mulP
#print axioms H2K5.Honest.value_single
#print axioms H2K5.Honest.value_pair
#print axioms H2K5.Honest.value_lineP
#print axioms H2K5.Honest.value_sumP
#print axioms H2K5.Honest.value_zero
#print axioms H2K5.Honest.length_addP
#print axioms H2K5.Honest.length_scaleP
#print axioms H2K5.Honest.length_mulP_cons
#print axioms H2K5.Honest.length_mulP_pair
#print axioms H2K5.Honest.length_lineP
#print axioms H2K5.Honest.length_foldl_addP_le
#print axioms H2K5.Honest.length_sumP_le
#print axioms H2K5.Honest.read_beyond
