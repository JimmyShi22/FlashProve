-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Lists.lean: the list functions of Honest/Sum.lean (`addL`,
`scaleL`, `padTo`, `sumPow`, `sumOf`, `psiL`), which compute in the program's type, READ IN A FIELD:
as polynomials (`polyOf`, Johnson/Desc/Part/MaskedSumSound.lean) and as sums in a variable's own way
(`Var.wt`, `Wt.sum`). Statements with their proofs. ρ: any reading.
Main names:
  `padTo_zero`, `padTo_cons`, `padTo_nil`, `padTo_length`, `padTo_getD`: a list cut or filled.
  `addL_getD`, `scaleL_getD`, `map_getD`: a member of a sum, of a multiple, of a list whose members
    are written anew without a change of their reading.
  `polyOf_addL`, `polyOf_scaleL`, `polyOf_padTo`, `polyOf_padTo_addL`, `polyOf_padTo_scaleL`,
    `polyOf_one`, `polyOf_psiL`: the same of polynomials.
  `sumPow_val`, `sumOf_val`: **at a list of the variable's length, the part's way of summing is the
    verifier's law's.**
  `sum_psi`, `sum_C`: the sum of psi is 1; the sum of a constant.

Limits. Nothing on a protocol. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Terms
import Johnson.Desc.Part.MaskedSumSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum
open OnBytes.Desc.First.P1 (Wt PsiOk)
open Polynomial

/-! ## A list cut or filled -/

theorem padTo_zero (a : List E) : padTo 0 a = [] := by simp [padTo]

theorem padTo_cons (n : Nat) (x : E) (a : List E) : padTo (n + 1) (x :: a) = x :: padTo n a := by
  simp [padTo]

theorem padTo_nil (n : Nat) : padTo (n + 1) [] = zeroE :: padTo n [] := by
  simp [padTo, List.replicate_succ]

theorem padTo_length : ∀ (n : Nat) (a : List E), (padTo n a).length = n
  | 0, a => by rw [padTo_zero]; rfl
  | n + 1, [] => by rw [padTo_nil, List.length_cons, padTo_length n []]
  | n + 1, x :: a => by rw [padTo_cons, List.length_cons, padTo_length n a]

theorem padTo_getD : ∀ (n : Nat) (a : List E) (i : Nat),
    (padTo n a).getD i zeroE = if i < n then a.getD i zeroE else zeroE
  | 0, a, i => by rw [padTo_zero]; simp
  | n + 1, [], 0 => by rw [padTo_nil]; simp
  | n + 1, [], i + 1 => by
    rw [padTo_nil, List.getD_cons_succ, padTo_getD n [] i]
    simp
  | n + 1, x :: a, 0 => by rw [padTo_cons]; simp
  | n + 1, x :: a, i + 1 => by
    rw [padTo_cons, List.getD_cons_succ, List.getD_cons_succ, padTo_getD n a i]
    simp

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## Members -/

theorem addL_getD : ∀ (a b : List E) (i : Nat),
    ρ.val ((addL a b).getD i zeroE) = ρ.val (a.getD i zeroE) + ρ.val (b.getD i zeroE)
  | [], b, i => by
    show ρ.val (b.getD i zeroE) = ρ.val (([] : List E).getD i zeroE) + _
    simp [ρ.zero]
  | x :: a, [], i => by
    show ρ.val ((x :: a).getD i zeroE) = _ + ρ.val (([] : List E).getD i zeroE)
    simp [ρ.zero]
  | x :: a, y :: b, 0 => ρ.add x y
  | x :: a, y :: b, i + 1 => by
    show ρ.val ((addE x y :: addL a b).getD (i + 1) zeroE) = _
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, addL_getD a b i]

theorem scaleL_getD (k : E) : ∀ (a : List E) (i : Nat),
    ρ.val ((scaleL k a).getD i zeroE) = ρ.val k * ρ.val (a.getD i zeroE)
  | [], i => by
    show ρ.val (([] : List E).getD i zeroE) = _
    simp [ρ.zero]
  | x :: a, 0 => ρ.mul k x
  | x :: a, i + 1 => by
    show ρ.val ((mulE k x :: scaleL k a).getD (i + 1) zeroE) = _
    rw [List.getD_cons_succ, List.getD_cons_succ, scaleL_getD k a i]

/-- Members that are written anew without a change of their reading. -/
theorem map_getD (cn : E → E) (hcn : ∀ x, ρ.val (cn x) = ρ.val x) : ∀ (a : List E) (i : Nat),
    ρ.val ((a.map cn).getD i zeroE) = ρ.val (a.getD i zeroE)
  | [], _ => rfl
  | x :: a, 0 => hcn x
  | x :: a, i + 1 => by
    rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ, map_getD cn hcn a i]

/-! ## Polynomials -/

theorem polyOf_addL (a b : List E) : polyOf ρ (addL a b) = polyOf ρ a + polyOf ρ b := by
  ext i
  rw [coeff_add, polyOf_coeff, polyOf_coeff, polyOf_coeff, addL_getD]

theorem polyOf_scaleL (k : E) (a : List E) : polyOf ρ (scaleL k a) = C (ρ.val k) * polyOf ρ a := by
  ext i
  rw [coeff_C_mul, polyOf_coeff, polyOf_coeff, scaleL_getD]

/-- A list that is not longer than n, filled to n, is the same polynomial. -/
theorem polyOf_padTo (n : Nat) (a : List E) (h : a.length ≤ n) :
    polyOf ρ (padTo n a) = polyOf ρ a := by
  ext i
  rw [polyOf_coeff, polyOf_coeff, padTo_getD]
  by_cases hi : i < n
  · rw [if_pos hi]
  · rw [if_neg hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem polyOf_padTo_addL (n : Nat) (a b : List E) :
    polyOf ρ (padTo n (addL a b)) = polyOf ρ (padTo n a) + polyOf ρ (padTo n b) := by
  ext i
  rw [coeff_add, polyOf_coeff, polyOf_coeff, polyOf_coeff, padTo_getD, padTo_getD, padTo_getD]
  by_cases hi : i < n
  · rw [if_pos hi, if_pos hi, if_pos hi, addL_getD]
  · rw [if_neg hi, if_neg hi, if_neg hi, ρ.zero, add_zero]

theorem polyOf_padTo_scaleL (n : Nat) (k : E) (a : List E) :
    polyOf ρ (padTo n (scaleL k a)) = C (ρ.val k) * polyOf ρ (padTo n a) := by
  ext i
  rw [coeff_C_mul, polyOf_coeff, polyOf_coeff, padTo_getD, padTo_getD]
  by_cases hi : i < n
  · rw [if_pos hi, if_pos hi, scaleL_getD]
  · rw [if_neg hi, if_neg hi, ρ.zero, mul_zero]

/-- A list of one member is a constant. -/
theorem polyOf_one (x : E) : polyOf ρ [x] = C (ρ.val x) := by
  simp [polyOf]

/-- The part's psi is the law's. -/
theorem polyOf_psiL (v : Var) : polyOf ρ (psiL v) = (v.wt ρ).psi := by
  cases v with
  | plain d =>
    show polyOf ρ [zeroE, oneE] = X
    simp [polyOf, ρ.zero, ρ.one]
  | point z d =>
    show polyOf ρ [oneE] = 1
    simp [polyOf, ρ.one]

theorem psiL_length (v : Var) : (psiL v).length ≤ 2 := by
  cases v with
  | plain d => exact Nat.le_refl 2
  | point z d => exact Nat.le_succ 1

/-! ## Sums -/

theorem sumPow_val (v : Var) (j : Nat) : ρ.val (sumPow v j) = (v.wt ρ).mom j := by
  cases v with
  | plain d =>
    cases j with
    | zero =>
      show ρ.val (addE oneE oneE) = (if (0 : Nat) = 0 then (2 : K) else 1)
      rw [ρ.add, ρ.one, if_pos rfl]
      norm_num
    | succ j =>
      show ρ.val oneE = (if j + 1 = 0 then (2 : K) else 1)
      rw [ρ.one, if_neg (Nat.succ_ne_zero j)]
  | point z d =>
    cases j with
    | zero =>
      show ρ.val oneE = (if (0 : Nat) = 0 then (1 : K) else ρ.val z)
      rw [ρ.one, if_pos rfl]
    | succ j =>
      show ρ.val z = (if j + 1 = 0 then (1 : K) else ρ.val z)
      rw [if_neg (Nat.succ_ne_zero j)]

/-- The terms of the part's sum, from the power s on. -/
theorem sumTerms_val (v : Var) : ∀ (g : List E) (s : Nat),
    sumVal ρ ((g.zipIdx s).map fun x => mulE x.1 (sumPow v x.2)) =
      ∑ i ∈ Finset.range g.length, (v.wt ρ).mom (s + i) * ρ.val (g.getD i zeroE)
  | [], s => by simp [sumVal]
  | x :: g, s => by
    rw [List.zipIdx_cons, List.map_cons, List.length_cons, Finset.sum_range_succ']
    have ih := sumTerms_val v g (s + 1)
    simp only [sumVal, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, ρ.mul, sumPow_val]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm, mul_comm (ρ.val x)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : s + 1 + i = s + (i + 1) := by omega
    rw [e]

/-- **At a list of the variable's length, the part's way of summing is the law's.** -/
theorem sumOf_val (v : Var) (g : List E) (h : g.length = v.d) :
    ρ.val (sumOf v g) = (v.wt ρ).sum (polyOf ρ g) := by
  unfold sumOf
  rw [total_val, sumTerms_val ρ v g 0, Wt.sum, Var.wt_d, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [polyOf_coeff, Nat.zero_add]

/-- The sum of psi is 1. -/
theorem sum_psi (v : Var) (h2 : 2 ≤ v.d) : (v.wt ρ).sum (v.wt ρ).psi = 1 :=
  (psiOk_wt ρ [v] (fun u hu => by rw [List.mem_singleton.1 hu]; exact h2) (v.wt ρ)
    (List.mem_singleton.2 rfl)).2

/-- The sum of a constant. -/
theorem sum_C (v : Var) (h2 : 1 ≤ v.d) (t : K) : (v.wt ρ).sum (C t) = (v.wt ρ).mom 0 * t := by
  rw [Wt.sum, Finset.sum_eq_single 0]
  · rw [coeff_C_zero]
  · intro b _ hb
    rw [coeff_C_ne_zero hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by rw [Var.wt_d]; omega)) h

end ProofFile.Honest.SumLaw

end

#print axioms ProofFile.Honest.SumLaw.padTo_zero
#print axioms ProofFile.Honest.SumLaw.padTo_cons
#print axioms ProofFile.Honest.SumLaw.padTo_nil
#print axioms ProofFile.Honest.SumLaw.padTo_length
#print axioms ProofFile.Honest.SumLaw.padTo_getD
#print axioms ProofFile.Honest.SumLaw.addL_getD
#print axioms ProofFile.Honest.SumLaw.scaleL_getD
#print axioms ProofFile.Honest.SumLaw.map_getD
#print axioms ProofFile.Honest.SumLaw.polyOf_addL
#print axioms ProofFile.Honest.SumLaw.polyOf_scaleL
#print axioms ProofFile.Honest.SumLaw.polyOf_padTo
#print axioms ProofFile.Honest.SumLaw.polyOf_padTo_addL
#print axioms ProofFile.Honest.SumLaw.polyOf_padTo_scaleL
#print axioms ProofFile.Honest.SumLaw.polyOf_one
#print axioms ProofFile.Honest.SumLaw.polyOf_psiL
#print axioms ProofFile.Honest.SumLaw.psiL_length
#print axioms ProofFile.Honest.SumLaw.sumPow_val
#print axioms ProofFile.Honest.SumLaw.sumTerms_val
#print axioms ProofFile.Honest.SumLaw.sumOf_val
#print axioms ProofFile.Honest.SumLaw.sum_psi
#print axioms ProofFile.Honest.SumLaw.sum_C
