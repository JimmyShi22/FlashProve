-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Alg/RoundValues.lean: the scalars that the honest prover of a sum-check sends, by explicit formulas
in values of the round polynomial.

`Alg.roundPoly` is taken by choice from a proof of existence. That is enough for statements and
proofs, but a prover is a program: what it sends has to be given by a formula. The values of the
round polynomial are sums of the summand (`Alg.sumOutL`), so they are explicit; here its
coefficients are computed from its values at the nodes 0, 1, ..., D:
    [X^k] q = ∑_j q(j) · [X^k] ℓ_j,
    [X^k] ℓ_j = (∏_(m ≠ j) (j - m))⁻¹ · (-1)^(D - k) · e_(D - k)(the nodes other than j),
with e_r the elementary symmetric sum. The definitions use sums, products and inverses in the field,
and no polynomial. The nodes must be distinct in the field.

Sources: on Mathlib's Lagrange interpolation and Vieta's formulas.
-/
import Alg.SumCheck
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace Alg

open Finset Polynomial

variable {K : Type} [Field K]

/-- The coefficient of X^k, k ≤ D, in the Lagrange basis polynomial number j for the nodes 0, ...,
D. -/
def lagCoeff (K : Type) [Field K] (D : ℕ) (j : Fin (D + 1)) (k : ℕ) : K :=
  (∏ m ∈ univ.erase j, (((j : ℕ) : K) - ((m : ℕ) : K)))⁻¹ *
    ((-1) ^ (D - k) * ∑ t ∈ (univ.erase j).powersetCard (D - k), ∏ m ∈ t, ((m : ℕ) : K))

/-- The coefficient of X^k, k ≤ D, of the polynomial of degree at most D with the values v 0, ...,
v D at the nodes 0, ..., D (the nodes distinct in the field: `coeff_eq_coeffOfValues`). -/
def coeffOfValues (D : ℕ) (v : ℕ → K) (k : ℕ) : K := ∑ j : Fin (D + 1), v j * lagCoeff K D j k

theorem coeff_basis (D : ℕ) (j : Fin (D + 1)) {k : ℕ} (hk : k ≤ D) :
    (Lagrange.basis univ (fun m : Fin (D + 1) => ((m : ℕ) : K)) j).coeff k = lagCoeff K D j k := by
  have hcard : Multiset.card ((univ.erase j).val.map fun m : Fin (D + 1) => ((m : ℕ) : K)) = D := by
    rw [Multiset.card_map, ← Finset.card_def, Finset.card_erase_of_mem (mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    rfl
  have h1 : Lagrange.basis univ (fun m : Fin (D + 1) => ((m : ℕ) : K)) j =
      C (∏ m ∈ univ.erase j, (((j : ℕ) : K) - ((m : ℕ) : K)))⁻¹ *
        (((univ.erase j).val.map fun m : Fin (D + 1) => ((m : ℕ) : K)).map fun t =>
          X - C t).prod := by
    unfold Lagrange.basis Lagrange.basisDivisor
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib, Multiset.map_map]
    rfl
  rw [h1, coeff_C_mul, Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; exact hk),
    hcard, Finset.esymm_map_val]
  rfl

/-- Under `hinj`, `hq`, `hk`: `coeffOfValues` gives the coefficients of q. -/
theorem coeff_eq_coeffOfValues {D : ℕ}
    (hinj : Function.Injective fun m : Fin (D + 1) => ((m : ℕ) : K)) (q : K[X])
    (hq : q.natDegree ≤ D) {k : ℕ} (hk : k ≤ D) :
    q.coeff k = coeffOfValues D (fun j => q.eval (j : K)) k := by
  have hdeg : q.degree < (univ : Finset (Fin (D + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hq)
  have h :=
    Lagrange.eq_interpolate (s := univ) (v := fun m : Fin (D + 1) => ((m : ℕ) : K)) hinj.injOn hdeg
  conv_lhs => rw [h]
  rw [Lagrange.interpolate_apply, finset_sum_coeff]
  unfold coeffOfValues
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul, coeff_basis D j hk]

/-- The scalars of a round from the values at 0, ..., e + 1: the value at 0 and the coefficients of
X^2, ..., X^(e+1). -/
def valueScalars (e : ℕ) (v : ℕ → K) : Fin (e + 1) → K :=
  Fin.cons (v 0) fun j : Fin e => coeffOfValues (e + 1) v ((j : ℕ) + 2)

/-- Under `hinj`, `hq`: `valueScalars` gives the scalars of the polynomial. -/
theorem valueScalars_eq {e : ℕ} (hinj : Function.Injective (node e : Fin (e + 2) → K))
    (q : K[X]) (hq : q.natDegree ≤ e + 1) :
    valueScalars e (fun k => q.eval (k : K)) = coeffScalars q := by
  unfold valueScalars coeffScalars
  congr 1
  · show q.eval ((0 : ℕ) : K) = q.coeff 0
    rw [Nat.cast_zero, ← coeff_zero_eq_eval_zero]
  · funext j
    exact (coeff_eq_coeffOfValues (D := e + 1) hinj q hq (by have := j.2; omega)).symm

/-- The nodes 0, 1 are distinct in every field. -/
theorem node_injective_zero : Function.Injective (node 0 : Fin (0 + 2) → K) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [node] at h ⊢

/-- The nodes 0, 1, 2 are distinct if 2 is not 0 in the field. -/
theorem node_injective_one (h2 : (2 : K) ≠ 0) : Function.Injective (node 1 : Fin (1 + 2) → K) := by
  have h21 : (2 : K) ≠ 1 := fun h => one_ne_zero (α := K) (by linear_combination h)
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [node, h2, h21, h21.symm, h2.symm] at h ⊢

/-- The nodes 0, ..., e + 1 are distinct if the characteristic is larger than e + 1. -/
theorem node_injective_of_lt_char (p : ℕ) [CharP K p] {e : ℕ} (he : e + 1 < p) :
    Function.Injective (node e : Fin (e + 2) → K) := by
  intro a b h
  have h' : ((a : ℕ) : K) = ((b : ℕ) : K) := h
  rw [CharP.natCast_eq_natCast K p] at h'
  have ha : (a : ℕ) < p := lt_of_le_of_lt (Nat.le_of_lt_succ a.2) he
  have hb : (b : ℕ) < p := lt_of_le_of_lt (Nat.le_of_lt_succ b.2) he
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h' ha hb)

/-- Under `hg`, `hd`, `hinj`: `valueScalars` of the sums of the summand gives the scalars of the
true round polynomial. -/
theorem valueScalars_roundPoly {ι : Type} [DecidableEq ι] {d : ι → ℕ} {g : (ι → K) → K}
    (hg : DegLE d g) (wt : ι → Bool → K) (i : ι) (rest : List ι) (z : ι → K) {e : ℕ}
    (hd : d i ≤ e + 1) (hinj : Function.Injective (node e : Fin (e + 2) → K)) :
    valueScalars e (fun k => sumOutL wt rest g (Function.update z i (k : K))) =
      coeffScalars (roundPoly hg wt i rest z) := by
  rw [← valueScalars_eq hinj _ ((natDegree_roundPoly_le hg wt i rest z).trans hd)]
  simp only [eval_roundPoly]

end Alg
