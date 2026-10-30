-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscVarsMixProofs.lean: the proofs of the statements of Cb/Ld/LdPscVarsMix.lean.
-/
import Cb.Ld.LdPscVarsMix
import Cb.Ld.LdPscVarsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Polynomial

section
variable (E : Type) [Field E] [Fintype E]

theorem psm_ok : Spec.psm_ok E := by
  intro n₁ n k D _ dom hn hD v hv
  rcases List.mem_cons.1 hv with rfl | h
  · exact psv_dom_ok E n₁ D dom hD
  · exact psv_plains_ok E n k hn v h

theorem psm_okW : Spec.psm_okW E := by
  intro n₁ n k D _ _ _ dom z₀ z hd v hv
  rcases List.mem_cons.1 hv with rfl | h
  · exact psv_lag_ok E n₁ D dom z₀ hd
  · exact psv_eqs_ok E n k z v h

theorem psm_sum : Spec.psm_sum E := by
  intro n₁ n k D _ dom f
  show ((pfDom E n₁ D).var (pdDom E n₁ dom)).sum (fun x =>
      hSumAll (pVars (List.replicate k (pfCube E n)) (pdPlains E n k)) fun xs => f (x, xs)) = _
  rw [psv_dom_sum]
  exact Finset.sum_congr rfl fun x _ => psv_plains_sum E n k _

theorem psm_sumW : Spec.psm_sumW E := by
  intro n₁ n k D _ _ dom z₀ z f
  show ((pfDom E n₁ D).var (pdLag E n₁ dom z₀)).sum (fun x =>
      hSumAll (pVars (List.replicate k (pfCube E n)) (pdEqs E n k z)) fun xs => f (x, xs)) = _
  rw [psv_lag_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [psv_eqs_sum, Finset.mul_sum]

omit [Fintype E] in
theorem psm_ext_at : Spec.psm_ext_at E := by
  intro k D _ _ dom u x b hd
  unfold pvExt
  rw [Finset.sum_eq_single x]
  · rw [Lagrange.eval_basis_self hd.injOn (Finset.mem_univ _), one_mul, Alg.mle_corner]
  · intro x' _ hx
    rw [Lagrange.eval_basis_of_ne hx (Finset.mem_univ _), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype E] in
theorem psm_ext_deg : Spec.psm_ext_deg E := by
  intro k m D _ _ dom u z hd hm
  have hp : (∑ x : D, C (Alg.mle (u x) z) * Lagrange.basis Finset.univ dom x).natDegree ≤ m := by
    refine natDegree_sum_le_of_forall_le _ _ fun x _ => (natDegree_C_mul_le _ _).trans ?_
    rw [Lagrange.natDegree_basis hd.injOn (Finset.mem_univ x), Finset.card_univ, hm]
    exact le_refl _
  refine ⟨fun t => (∑ x : D, C (Alg.mle (u x) z) * Lagrange.basis Finset.univ dom x).coeff t,
    fun x₀ => ?_⟩
  rw [hev_of_poly E _ hp, eval_finset_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [eval_mul, eval_C, mul_comm]

omit [Fintype E] in
theorem psm_ext_lin : Spec.psm_ext_lin E := by
  intro k D _ _ dom u x₀ z
  unfold pvExt Alg.mle
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => by ring

theorem psm_ext_sum : Spec.psm_ext_sum E := by
  intro n₁ n k D _ _ dom z₀ z u hd
  rw [psm_sumW]
  unfold pvExt Alg.mle
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := psm_ext_at E k D dom u x b hd
  unfold pvExt Alg.mle at h
  show _ * (_ * ∑ x', eval (dom x) (Lagrange.basis Finset.univ dom x') *
          ∑ b', Alg.eqk
              (hFnOf (pfCube E n) k (pdEqs E n k z)
                (pH _ (pdEqs E n k z) (ppOf (pfCube E n) k (Alg.corner b)))) b' * u x' b') = _
  rw [psv_fn_pt, h]

end
end Cb
