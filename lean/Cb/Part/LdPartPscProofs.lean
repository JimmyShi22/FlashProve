-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartPscProofs.lean: the proofs of the statements of Cb/Part/LdPartPsc.lean (a sum of
terms over maps ↦ the parameters of a sumcheck).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Of general use: `ldPart_degLE_sum`, `ldPart_degLE_prod`; `ldPart_line_prod`, `ldPart_line_sum` (a
sum of products of values, each moving on a line, is a polynomial whose degree is at most the length
of the longest product); `ldPartPsc_vars`, `ldPartPsc_inj`, `ldPartPsc_degX`, `ldPartPsc_degY`.
Nothing else is said here.
-/
import Cb.Part.LdPartPsc
import Cb.Part.LdPartVarsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Polynomial

section Lists
variable {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] {α : Type}

theorem ldPart_degLE_sum (l : List α) (d : ι → ℕ)
    (g : α → (ι → K) → K) (h : ∀ t ∈ l, Alg.DegLE d (g t)) :
    Alg.DegLE d fun z => (l.map fun t => g t z).sum := by
  induction l with
  | nil => simpa using Alg.DegLE.const d (0 : K)
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (h a List.mem_cons_self).add (ih fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem ldPart_degLE_prod (l : List α) (d : α → ι → ℕ)
    (g : α → (ι → K) → K) (h : ∀ a, Alg.DegLE (d a) (g a)) :
    Alg.DegLE (fun i => (l.map fun a => d a i).sum) fun z => (l.map fun a => g a z).prod := by
  induction l with
  | nil => simpa using Alg.DegLE.const (fun _ : ι => 0) (1 : K)
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      exact (h a).mul ih

end Lists

section Lines
variable {E : Type} [Field E] {A T : Type}

theorem ldPart_line_prod (l : List A) (v u : A → E) :
    ∃ q : E[X], q.natDegree ≤ l.length ∧ ∀ y, q.eval y = (l.map fun a => v a + u a * y).prod := by
  induction l with
  | nil => exact ⟨1, by simp, by simp⟩
  | cons a l ih =>
      obtain ⟨q, hq, he⟩ := ih
      have h1 : (C (v a) + C (u a) * X : E[X]).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans
          (max_le ((natDegree_C (v a)).le.trans (Nat.zero_le 1))
            ((natDegree_C_mul_le (u a) X).trans natDegree_X_le))
      refine ⟨(C (v a) + C (u a) * X) * q, natDegree_mul_le.trans ?_, fun y => ?_⟩
      · rw [List.length_cons]
        omega
      · rw [eval_mul, he, List.map_cons, List.prod_cons]
        simp

theorem ldPart_line_sum (l : List T) (c : T → E) (at' : T → List A) (D : ℕ)
    (h : ∀ t ∈ l, (at' t).length ≤ D) (v u : A → E) :
    ∃ q : E[X],
      q.natDegree ≤ D ∧
      ∀ y, q.eval y = (l.map fun t => c t * ((at' t).map fun a => v a + u a * y).prod).sum := by
  induction l with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons t l ih =>
      obtain ⟨q, hq, he⟩ := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
      obtain ⟨p, hp, hpe⟩ := ldPart_line_prod (at' t) v u
      refine ⟨C (c t) * p + q,
        natDegree_add_le_of_degree_le
          ((natDegree_C_mul_le _ _).trans (hp.trans (h t List.mem_cons_self))) hq,
        fun y => ?_⟩
      rw [eval_add, eval_mul, eval_C, hpe, he, List.map_cons, List.sum_cons]

end Lines

section
variable {E St J : Type} [Field E] [Fintype E] [Fintype J] (S : LdPartSm E St J) (M : LdPartMk S)

theorem ldPartPsc_vars (h : ∀ st i, S.w st i = none → 1 ≤ M.n i) : (S.our M).VarsOK := fun st =>
  ldPartVars_ok E S.k M.n (S.w st) (h st)

theorem ldPartPsc_inj : (S.our M).ValInj := ldPartVars_inj E S.k M.n

theorem ldPartPsc_degX (da : S.A → Fin S.k → ℕ) (h : S.OK M da) : (S.our M).DegX := by
  intro st m u
  have hg : Alg.DegLE M.n fun z => S.pol st z fun a => S.F st m a z + u a := by
    unfold LdPartSm.pol
    refine ldPart_degLE_sum S.terms M.n
      (fun (t : LdPartTm E St S.A S.k) z =>
        t.coef st z * (t.atoms.map fun a => S.F st m a z + u a).prod) fun t ht => ?_
    obtain ⟨dc, h1, h2⟩ := h.fit t ht
    exact ((h1 st).mul
      (ldPart_degLE_prod t.atoms da (fun a z => S.F st m a z + u a) fun a =>
        (h.map st m a).add (Alg.DegLE.const _ (u a)))).mono h2
  have e : (fun X =>
        (S.our M).S0 st X (fun a => (S.our M).F st m a X + u a) +
          ∑ b, (S.our M).S1 st X (fun a => (S.our M).F st m a X + u a) b * (S.our M).Fb st m b X) =
      fun X => (fun z => S.pol st z fun a => S.F st m a z + u a) (S.fn M st X) := by
    funext X
    exact (congrArg _ (Fintype.sum_empty _)).trans (add_zero _)
  exact Eq.mpr (congrArg (HDeg ((S.our M).vars st)) e) (ldPartVars_deg E S.k M.n _ _ hg)

theorem ldPartPsc_degY (h : ∀ t ∈ S.terms, t.atoms.length ≤ M.DY) : (S.our M).DegY := by
  intro st P v u r
  obtain ⟨q, hq, he⟩ :=
    ldPart_line_sum S.terms (fun t => t.coef st (S.fn M st P)) (fun t => t.atoms) M.DY h v u
  refine ⟨fun t => q.coeff t, fun y => ?_⟩
  rw [hev_of_poly E q hq, he]
  exact (congrArg _ (Fintype.sum_empty _)).trans (add_zero _)

end

section
variable (E : Type) [Field E] [Fintype E]

theorem ldPartPsc_ok : Spec.ldPartPsc_ok E := fun _ _ _ S M da h =>
  ⟨ldPartPsc_vars S M h.plain, ldPartPsc_inj S M, ldPartPsc_degX S M da h, ldPartPsc_degY S M h.dy⟩

theorem ldPartPsc_sum : Spec.ldPartPsc_sum E := by
  intro St J _ S M τ st m
  have e : ∀ b : Fin S.k → Bool,
      (S.our M).sum st m (pH _ (ldPartDat E S.k M.n (S.w st)) (ldPartPP S.k M.n (Alg.corner b))) =
        S.val st m (Alg.corner b) := by
    intro b
    refine ((congrArg _ (Fintype.sum_empty _)).trans (add_zero _)).trans ?_
    show S.pol st (ldPartFn S.k M.n _ (pH _ _ (ldPartPP S.k M.n (Alg.corner b))))
        (fun a => S.F st m a (ldPartFn S.k M.n _ (pH _ _ (ldPartPP S.k M.n (Alg.corner b))))) = _
    rw [ldPartVars_fn]
    rfl
  show hSumAll (pVars (ldPartFmt E S.k M.n) (ldPartDat E S.k M.n (S.w st))) ((S.our M).sum st m) +
        ∑ j, M.slS st j * m j = τ ↔
    _
  rw [ldPartVars_sum]
  simp only [e]

theorem ldPartPsc_val : Spec.ldPartPsc_val E := by
  intro St J _ S M o m a
  unfold LdPartSm.outPt LdPartSm.outB
  rw [← ldPartVars_ini E S.k M.n (ldPartDat E S.k M.n (S.w o.st))
        (pDummy E M.DY) (pDummyD E M.DY) o.pt,
    ← ldPartVars_last E S.k M.n (ldPartDat E S.k M.n (S.w o.st))
      (pDummy E M.DY) (pDummyD E M.DY) o.pt]
  exact Iff.rfl

theorem ldPartPsc_s0 : Spec.ldPartPsc_s0 E := by
  intro St J _ S M o
  unfold LdPartSm.outPt
  rw [← ldPartVars_ini E S.k M.n (ldPartDat E S.k M.n (S.w o.st))
      (pDummy E M.DY) (pDummyD E M.DY) o.pt]
  rfl

end
end Cb
