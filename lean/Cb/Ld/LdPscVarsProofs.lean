-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscVarsProofs.lean: the proofs of the statements of Cb/Ld/LdPscVars.lean.

Of general use, at the end:
  `hdeg_of_degLE`: a function of k coordinates with degree at most n in each (`Alg.DegLE`) has the
    degrees of k variables of one format with degree n (`HDeg`).
  `degY_prod`: a product of r values, each moving on a line, is a polynomial of degree at most r
    (the condition `DegY` for a product of r revealed maps).
-/
import Cb.Ld.LdPscVars
import Cb.Ld.LdHideProofs
import Alg.Poly

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Polynomial

section
variable (E : Type) [Field E] [Fintype E]

omit [Fintype E] in
theorem hev_pvConst (n : ℕ) (c x : E) : hev (pvConst E n c) x = c := by
  unfold hev pvConst
  rw [Finset.sum_eq_single 0]
  · simp
  · intro t _ ht
    have : (t : ℕ) ≠ 0 := fun h => ht (Fin.ext h)
    simp [this]
  · simp

omit [Fintype E] in
/-- a vector of coefficients as a polynomial -/
theorem hev_as_poly {n : ℕ} (c : Fin (n + 1) → E) :
    ∃ p : E[X], p.natDegree ≤ n ∧ ∀ x, hev c x = p.eval x := by
  refine ⟨∑ t : Fin (n + 1), C (c t) * X ^ (t : ℕ), ?_, fun x => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · simp only [hev, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _

omit [Fintype E] in
/-- a polynomial as a vector of coefficients -/
theorem hev_of_poly {n : ℕ} (p : E[X]) (hp : p.natDegree ≤ n) (x : E) :
    hev (fun t : Fin (n + 1) => p.coeff t) x = p.eval x := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp),
    ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * x ^ i) (n + 1)]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

theorem psv_plain_var : Spec.psv_plain_var E := fun _ => rfl

theorem psv_plain_sum : Spec.psv_plain_sum E := by
  intro n g
  show ∑ b : Bool, (1 : E) • g (if b then (1 : E) else 0) = _
  rw [Fintype.sum_bool]
  simp [add_comm]

theorem psv_plain_ok : Spec.psv_plain_ok E := fun n hn => plain_ok E n hn

theorem psv_eq_sum : Spec.psv_eq_sum E := by
  intro n z g
  show ∑ b : Bool, (if b then z else 1 - z) • g (if b then (1 : E) else 0) = _
  rw [Fintype.sum_bool]
  simp [add_comm]

theorem psv_eq_ok : Spec.psv_eq_ok E := by
  intro n z
  show ((pfCube E n).var (pdEq E n z)).sum (hev (pvConst E n 1)) = 1
  rw [psv_eq_sum, hev_pvConst, hev_pvConst]
  ring

theorem psv_eq_lin : Spec.psv_eq_lin E := by
  intro n z c₀ c₁
  rw [psv_eq_sum]
  ring

theorem psv_dom_sum : Spec.psv_dom_sum E := by
  intro n D _ dom g
  show ∑ x, (1 : E) • g (dom x) = _
  simp

theorem psv_dom_ok : Spec.psv_dom_ok E := by
  intro n D _ dom hD
  show ((pfDom E n D).var (pdDom E n dom)).sum (hev (pvConst E n (Fintype.card D : E)⁻¹)) = 1
  rw [psv_dom_sum]
  simp only [hev_pvConst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ hD

theorem psv_lag_sum : Spec.psv_lag_sum E := fun _ _ _ _ _ _ _ => rfl

theorem psv_lag_ok : Spec.psv_lag_ok E := by
  intro n D _ _ _ dom z hd
  show ((pfDom E n D).var (pdLag E n dom z)).sum (hev (pvConst E n 1)) = 1
  rw [psv_lag_sum]
  simp only [hev_pvConst, mul_one]
  rw [← eval_finset_sum, Lagrange.sum_basis hd.injOn Finset.univ_nonempty, eval_one]

theorem psv_lag_at : Spec.psv_lag_at E := by
  intro n D _ _ dom x₀ g hd
  rw [psv_lag_sum, Finset.sum_eq_single x₀]
  · rw [Lagrange.eval_basis_self hd.injOn (Finset.mem_univ _), one_mul]
  · intro x _ hx
    rw [Lagrange.eval_basis_of_ne hx (Finset.mem_univ _), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem psv_lag_eval : Spec.psv_lag_eval E := by
  intro n m D _ _ dom z c hd hm
  obtain ⟨p, hp, he⟩ := hev_as_poly E c
  have hdeg : p.degree < (Finset.univ : Finset D).card := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    rw [Finset.card_univ]
    exact_mod_cast (by omega : p.natDegree < Fintype.card D)
  have h := Lagrange.eq_interpolate hd.injOn hdeg
  rw [psv_lag_sum, he z]
  conv_rhs => rw [h, Lagrange.interpolate_apply, eval_finset_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [eval_mul, eval_C, he, mul_comm]

theorem psv_val : Spec.psv_val E := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem psv_plains_ok : Spec.psv_plains_ok E := by
  intro n k hn
  induction k with
  | zero => intro v hv; exact absurd hv (List.not_mem_nil)
  | succ k ih =>
      intro v hv
      rcases List.mem_cons.1 hv with rfl | h
      · exact psv_plain_ok E n hn
      · exact ih v h

theorem psv_eqs_ok : Spec.psv_eqs_ok E := by
  intro n k
  induction k with
  | zero => intro _ v hv; exact absurd hv (List.not_mem_nil)
  | succ k ih =>
      intro z v hv
      rcases List.mem_cons.1 hv with rfl | h
      · exact psv_eq_ok E n (z 0)
      · exact ih _ v h

omit [Field E] [Fintype E] in
theorem psv_fn_pt : Spec.psv_fn_pt E := by
  intro f k
  induction k with
  | zero => intro _ x; exact Subsingleton.elim _ _
  | succ k ih =>
      intro d x
      show (Fin.cons (x 0)
          (hFnOf f k d.2
            (pH (List.replicate k f) d.2 (ppOf f k fun i => x i.succ))) : Fin (k + 1) → E) = x
      rw [ih]
      exact Fin.cons_self_tail x

omit [Fintype E] in
theorem eqk_cons_fn {k : ℕ} (z : Fin (k + 1) → E) (β : Bool) (b : Fin k → Bool) :
    Alg.eqk z (Fin.cons β b) = (if β then z 0 else 1 - z 0) * Alg.eqk (fun i => z i.succ) b := by
  simp [Alg.eqk, Fin.prod_univ_succ]

theorem psv_eqs_sum : Spec.psv_eqs_sum E := by
  intro n k
  induction k with
  | zero =>
      intro z f
      show f () = ∑ b : Fin 0 → Bool, Alg.eqk z b * f ()
      simp [Alg.eqk]
  | succ k ih =>
      intro z f
      show ((pfCube E n).var (pdEq E n (z 0))).sum (fun x =>
          hSumAll (pVars (List.replicate k (pfCube E n)) (pdEqs E n k fun i => z i.succ))
            fun xs => f (x, xs)) = _
      rw [psv_eq_sum, ih, ih, Alg.sum_cube_succ, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [eqk_cons_fn, eqk_cons_fn]
      simp only [if_true, Bool.false_eq_true, if_false]
      exact congrArg₂ (· + ·) (mul_assoc _ _ _).symm (mul_assoc _ _ _).symm

theorem psv_plains_sum : Spec.psv_plains_sum E := by
  intro n k
  induction k with
  | zero =>
      intro f
      show f () = ∑ b : Fin 0 → Bool, f ()
      simp
  | succ k ih =>
      intro f
      show ((pfCube E n).var (pdPlain E n)).sum (fun x =>
          hSumAll (pVars (List.replicate k (pfCube E n)) (pdPlains E n k)) fun xs => f (x, xs)) = _
      rw [psv_plain_sum, ih, ih, Alg.sum_cube_succ, ← Finset.sum_add_distrib]
      rfl

theorem psv_eqs_mle : Spec.psv_eqs_mle E := by
  intro n k z u
  rw [psv_eqs_sum]
  unfold Alg.mle
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [psv_fn_pt]
  exact congrArg _ (Alg.mle_corner u b)

end

section General
variable {E : Type} [Field E]

theorem hdeg_of_degLE (f : PFmt E) :
    ∀ (k : ℕ) (d : PDats (List.replicate k f)) (g : (Fin k → E) → E), Alg.DegLE (fun _ => f.n) g →
      HDeg (pVars (List.replicate k f) d) fun X => g (hFnOf f k d X) := by
  intro k
  induction k with
  | zero => intro _ _ _; trivial
  | succ k ih =>
      intro d g hg
      refine ⟨fun xs => ?_, fun x => ih d.2 (fun z => g (Fin.cons x z)) fun z i => ?_⟩
      · obtain ⟨q, hq, he⟩ := hg (Fin.cons 0 (hFnOf f k d.2 xs)) 0
        refine ⟨fun t => q.coeff t, fun x => ?_⟩
        rw [hev_of_poly E q hq, ← he, Fin.update_cons_zero]
        rfl
      · obtain ⟨q, hq, he⟩ := hg (Fin.cons x z) i.succ
        refine ⟨q, hq, fun t => ?_⟩
        show g (Fin.cons x (Function.update z i t)) = _
        rw [← he, Fin.cons_update]

/-- A product of r values, each moving on a line, is a polynomial of degree at most r. -/
theorem degY_prod (r : ℕ) (v u : Fin r → E) :
    ∃ c : Fin (r + 1) → E, ∀ y : E, ∏ a, (v a + u a * y) = hev c y := by
  have h1 : ∀ a : Fin r, (C (v a) + C (u a) * X : E[X]).natDegree ≤ 1 := fun a =>
    (natDegree_add_le _ _).trans
      (max_le ((natDegree_C (v a)).le.trans (Nat.zero_le 1))
        ((natDegree_C_mul_le (u a) X).trans natDegree_X_le))
  have h2 :=
    natDegree_prod_le (Finset.univ : Finset (Fin r)) fun a => (C (v a) + C (u a) * X : E[X])
  have h3 : ∑ a : Fin r, (C (v a) + C (u a) * X : E[X]).natDegree ≤ r :=
    (Finset.sum_le_sum fun a _ => h1 a).trans (by simp)
  refine ⟨fun t => (∏ a : Fin r, (C (v a) + C (u a) * X : E[X])).coeff t, fun y => ?_⟩
  rw [hev_of_poly E _ (h2.trans h3), eval_prod]
  exact Finset.prod_congr rfl fun a _ => by simp

end General
end Cb
