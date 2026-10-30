-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpEndUProofs.lean: the proofs of the statements of Cb/Ld/LdLkpEndU.lean (on the end claim
of the table's product trees).
-/
import Cb.Ld.LdLkpEndU
import Cb.Ld.LdLkpBitProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpEndU_sum : Spec.ldLkpEndU_sum E := by
  intro B x m
  have e : hSumAll (B.par.vars x.2) (B.par.sum x.2 m) =
      Alg.mle (fun b => 1 + m (B.tAt b) * B.cp x.2 b) (B.z x.2) := by
    show hSumAll (pVars (List.replicate B.k (pfCube E 2)) (pdEqs E 2 B.k (B.z x.2)))
        (B.par.sum x.2 m) = _
    rw [psv_eqs_sum E]
    unfold Alg.mle
    refine Finset.sum_congr rfl fun b _ => ?_
    have hx : B.fn x.2 (pH _ (pdEqs E 2 B.k (B.z x.2)) (ppOf (pfCube E 2) B.k (Alg.corner b))) =
        Alg.corner b :=
      psv_fn_pt E (pfCube E 2) B.k (pdEqs E 2 B.k (B.z x.2)) (Alg.corner b)
    have hs : B.par.sum x.2 m
          (pH _ (pdEqs E 2 B.k (B.z x.2)) (ppOf (pfCube E 2) B.k (Alg.corner b))) =
        1 + m (B.tAt b) * B.cp x.2 b := by
      show 1 + ∑ _u : Unit, Alg.mle (B.cp x.2) (B.fn x.2 _) * B.Y m (B.fn x.2 _) = _
      rw [hx]
      unfold LkEndU.Y
      rw [Alg.mle_corner, Alg.mle_corner]
      simp [mul_comm]
    exact congrArg (fun s => Alg.eqk (B.z x.2) b * s) hs
  show hSumAll (B.par.vars x.2) (B.par.sum x.2 m) + ∑ j, B.inc x.2 j * m j = x.1 ↔ _
  rw [e]
  exact Iff.rfl

theorem ldLkpEndU_vars : Spec.ldLkpEndU_vars E := fun B =>
  ⟨fun s => psv_eqs_ok E 2 B.k (B.z s),
    fun f hf => by rw [List.eq_of_mem_replicate hf]; exact (psv_val E).1 2⟩

theorem ldLkpEndU_deg : Spec.ldLkpEndU_deg E := by
  intro B st (m : B.J → E)
  have hg : Alg.DegLE (fun _ : Fin B.k => (pfCube E 2).n) fun z =>
      1 + Alg.mle (B.cp st) z * B.Y m z :=
    (Alg.DegLE.const _ 1).add (((Alg.DegLE.mle _).mul (Alg.DegLE.mle _)).mono fun _ => le_refl _)
  have h := hdeg_of_degLE (pfCube E 2) B.k (pdEqs E 2 B.k (B.z st)) _ hg
  have e : B.par.sum st m =
      fun X =>
        1 + Alg.mle (B.cp st) (hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.z st)) X) *
              B.Y m (hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.z st)) X) := by
    funext X
    show 1 + ∑ _u : Unit, Alg.mle (B.cp st) (B.fn st X) * B.Y m (B.fn st X) = _
    simp
  rw [e]
  exact h

theorem ldLkpEndU_joint : Spec.ldLkpEndU_joint E := by
  intro B Ex Wt Kc A0 msg
  have e : B.par.SumHolds = B.Holds :=
    funext fun x => funext fun m => propext (ldLkpEndU_sum E B x m)
  unfold PscPar.baseIn PscPar.baseRels
  rw [e]
  rfl

theorem ldLkpEndU_goodAt : Spec.ldLkpEndU_goodAt E := by
  intro B Ex M Wp Kc A0 msg
  rw [ldLkpEndU_joint E]
  exact psc_core_goodAt E B.par Ex M Wp Kc A0 msg (ldLkpEndU_vars E B).1
    (ldLkpEndU_deg E B) (ldLkpEndU_vars E B).2

theorem ldLkpEndU_good : Spec.ldLkpEndU_good E := by
  intro B S E₀ Wp Kc A0 msg
  rw [ldLkpEndU_joint E]
  exact psc_core_goodB_sig E S B.par E₀ Wp Kc A0 msg (ldLkpEndU_vars E B).1
    (ldLkpEndU_deg E B) (ldLkpEndU_vars E B).2

theorem LkEndU.linB (B : LkEndU E) : B.par.LinB B.rowB := by
  intro s m b X
  classical
  show Alg.mle (fun b => m (B.tAt b)) (B.fn s X) = ∑ j, B.rowB s b X j * m j
  unfold LkEndU.rowB Alg.mle
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h := Finset.sum_ite_eq Finset.univ (B.tAt c) fun j => Alg.eqk (B.fn s X) c * m j
  rw [if_pos (Finset.mem_univ _)] at h
  refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  congr

theorem ldLkpEndU_row : Spec.ldLkpEndU_row E := by
  intro B zz m
  haveI hA : IsEmpty B.par.A := inferInstanceAs (IsEmpty Empty)
  have h1 := psc_mid_empty E B.par hA zz m
  have e : (⟨zz.st, zz.eps, zz.pt, zz.fin, isEmptyElim⟩ : B.par.Out) = B.outOf zz := by
    unfold LkEndU.outOf
    congr
    funext a
    exact a.elim
  rw [e] at h1
  exact h1.trans (psc_row_U E B.par B.rowB (B.linB E) (B.outOf zz) m)

theorem ldLkpEndU_tg : Spec.ldLkpEndU_tg E := fun B zz => by
  show zz.fin - zz.eps * 1 = _
  rw [mul_one]

theorem ldLkpEndU_len : Spec.ldLkpEndU_len E := fun B Ex => by
  show (pRound0 E :: (List.replicate B.k (pfCube E 2)).map pRound).length = _
  simp

end
end Cb
