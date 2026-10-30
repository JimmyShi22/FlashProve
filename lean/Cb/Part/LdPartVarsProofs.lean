-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartVarsProofs.lean: the proofs of the statements of Cb/Part/LdPartVars.lean (cube
variables with a degree and a form for each; points as functions). Each is an induction on the
number of variables, after the pattern of Cb/Ld/LdPscVarsProofs.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Besides these proofs only the helper `ldPartVars_sum1`. Nothing else is said here.
-/
import Cb.Part.LdPartVars
import Cb.Ld.LdPscVarsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Polynomial

section
variable (E : Type) [Field E] [Fintype E]

theorem ldPartVars_ok : Spec.ldPartVars_ok E := by
  intro k
  induction k with
  | zero => intro _ _ _ v hv; exact absurd hv List.not_mem_nil
  | succ k ih =>
      intro n w h v hv
      rcases List.mem_cons.1 hv with rfl | h'
      · show ((pfCube E (n 0)).var (ldPartDat1 E (n 0) (w 0))).OK
        cases hw : w 0 with
        | none => exact psv_plain_ok E (n 0) (h 0 hw)
        | some z => exact psv_eq_ok E (n 0) z
      · exact ih _ _ (fun i hi => h i.succ hi) v h'

theorem ldPartVars_inj : Spec.ldPartVars_inj E := by
  intro k
  induction k with
  | zero => intro _ f hf; exact absurd hf List.not_mem_nil
  | succ k ih =>
      intro n f hf
      rcases List.mem_cons.1 hf with rfl | h'
      · exact fun _ _ h => h
      · exact ih _ f h'

/-- the sum over one variable, by its weights -/
theorem ldPartVars_sum1 (n : ℕ) (w : Option E) (g : E → E) :
    ((pfCube E n).var (ldPartDat1 E n w)).sum g =
      ldPartWt w false * g 0 + ldPartWt w true * g 1 := by
  cases w with
  | none =>
      show ((pfCube E n).var (pdPlain E n)).sum g = 1 * g 0 + 1 * g 1
      rw [psv_plain_sum, one_mul, one_mul]
  | some z => exact psv_eq_sum E n z g

theorem ldPartVars_sum : Spec.ldPartVars_sum E := by
  intro k
  induction k with
  | zero =>
      intro n w f
      show f () = ∑ b : Fin 0 → Bool, (∏ i : Fin 0, ldPartWt (w i) (b i)) * f ()
      simp
  | succ k ih =>
      intro n w f
      show ((pfCube E (n 0)).var (ldPartDat1 E (n 0) (w 0))).sum (fun x =>
          hSumAll (pVars (ldPartFmt E k fun i => n i.succ)
              (ldPartDat E k (fun i => n i.succ) fun i => w i.succ))
            fun xs => f (x, xs)) = _
      rw [ldPartVars_sum1, ih, ih, Alg.sum_cube_succ, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      exact congrArg₂ (· + ·) (mul_assoc _ _ _).symm (mul_assoc _ _ _).symm

theorem ldPartVars_fn : Spec.ldPartVars_fn E := by
  intro k
  induction k with
  | zero => intro _ _ x; exact Subsingleton.elim _ _
  | succ k ih =>
      intro n d x
      show (Fin.cons (x 0)
          (ldPartFn k (fun i => n i.succ) d.2
            (pH _ d.2 (ldPartPP k (fun i => n i.succ) fun i => x i.succ))) : Fin (k + 1) → E) = x
      rw [ih]
      exact Fin.cons_self_tail x

theorem ldPartVars_deg : Spec.ldPartVars_deg E := by
  intro k
  induction k with
  | zero => intro _ _ _ _; trivial
  | succ k ih =>
      intro n d g hg
      refine ⟨fun xs => ?_,
        fun x => ih (fun i => n i.succ) d.2 (fun z => g (Fin.cons x z)) fun z i => ?_⟩
      · obtain ⟨q, hq, he⟩ := hg (Fin.cons 0 (ldPartFn k (fun i => n i.succ) d.2 xs)) 0
        refine ⟨fun t => q.coeff t, fun x => ?_⟩
        rw [hev_of_poly E q hq, ← he, Fin.update_cons_zero]
        rfl
      · obtain ⟨q, hq, he⟩ := hg (Fin.cons x z) i.succ
        refine ⟨q, hq, fun t => ?_⟩
        show g (Fin.cons x (Function.update z i t)) = _
        rw [← he, Fin.cons_update]

theorem ldPartVars_ini : Spec.ldPartVars_ini E := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; exact Subsingleton.elim _ _
  | succ k ih =>
      intro n d g e γ
      show (Fin.cons γ.1
          (ldPartFn k (fun i => n i.succ) d.2
            (hInit _ d.2 g e (pH _ (PDats.snoc _ d.2 g e) γ.2))) : Fin (k + 1) → E) =
        Fin.cons γ.1 (ldPartIni k (fun i => n i.succ) g γ.2)
      rw [ih]

theorem ldPartVars_last : Spec.ldPartVars_last E := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; rfl
  | succ k ih => intro n d g e γ; exact ih (fun i => n i.succ) d.2 g e γ.2

theorem ldPartVars_len : Spec.ldPartVars_len E := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih => intro n; exact congrArg (· + 1) (ih fun i => n i.succ)

theorem ldPartVars_degs : Spec.ldPartVars_degs E := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro n
      rw [List.ofFn_succ]
      exact congrArg (n 0 :: ·) (ih fun i => n i.succ)

end
end Cb
