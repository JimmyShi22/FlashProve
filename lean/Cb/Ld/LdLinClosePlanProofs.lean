-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlan.lean (the rows
that the test for linear constraints leaves, as rows on two groups; the plan without a splitting).
Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdLinClosePlan.lean):
  `ldLinPlan_rows₁`: the rows on the first group G₁
  `ldLinPlan_rows₂`: the rows on the second group G₂
  `ldLinPlan_says`: what the plan's base joint `p.base B'` says
-/
import Cb.Ld.LdLinClosePlan

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem Slf.plus_val {E St J : Type} [Field E] [Fintype J]
    (s₁ s₂ : Slf E St J) (st : St) (u : J → E) :
    (s₁.plus s₂).val st u = s₁.val st u + s₂.val st u := by
  unfold Slf.val Slf.plus
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => add_mul _ _ _

section
variable (E ι κ J Y : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype ι] in
theorem ldLinPlan_rows₁ : Spec.ldLinPlan_rows₁ E ι κ J Y := by
  intro C p st m
  have hrec : ∀ s, (p.sl₁ (.inl (.inl s))).val (C.sh st) (p.G₁.msg m) =
      C.D.X.Z.val st.1.1.1.2.1 (C.D.X.msg (C.uM m)) s := by
    intro s
    show (p.G₁.onMem C.nU p.hU _).val (C.sh st) (p.G₁.msg m) = _
    rw [ldForm_onMem, ldForm_push]
    rfl
  have hcol : ∀ i, (p.sl₁ (.inl (.inr i))).val (C.sh st) (p.G₁.msg m) =
      C.D.X.G.mulVec (C.uM m) (st.1.2.1 i) := by
    intro i
    show (p.G₁.onMem C.nU p.hU _).val (C.sh st) (p.G₁.msg m) = _
    rw [ldForm_onMem, ldForm_push]
    rfl
  have hfold : ∀ u : Unit, (p.sl₁ (.inr u)).val (C.sh st) (p.G₁.msg m) =
      (∑ y, Alg.eqk st.2 (C.D.py y) * C.oM m y) -
        ∑ y, Alg.eqk st.2 (C.D.py y) * C.D.omU (C.D.X.msg (C.uM m)) st.1.1.2.2 y := by
    intro u
    show (Slf.sub (p.G₁.onMem C.nO p.hO _) (p.G₁.onMem C.nU p.hU _)).val (C.sh st) (p.G₁.msg m) = _
    rw [ldForm_sub, ldForm_onMem, ldForm_onMem, ldForm_push, ldForm_push, Fintype.sum_prod_type]
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun y _ => ?_)
    unfold LdLinW.omU
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  constructor
  · intro h
    exact ⟨funext fun s => (hrec s).symm.trans (h (.inl (.inl s))),
      fun i => (hcol i).symm.trans (h (.inl (.inr i))),
      sub_eq_zero.1 ((hfold ()).symm.trans (h (.inr ())))⟩
  · rintro ⟨h1, h2, h3⟩ ((s | i) | u)
    · exact (hrec s).trans (congrFun h1 s)
    · exact (hcol i).trans (h2 i)
    · exact (hfold u).trans (sub_eq_zero.2 h3)

omit [Fintype ι] [Fintype κ] [Fintype J] in
theorem ldLinPlan_rows₂ : Spec.ldLinPlan_rows₂ E ι κ J Y := by
  intro C p st m hr
  have hev : ∀ u : Unit, (p.sl₂ (.inl u)).val st (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) =
      Alg.mle (C.wM m) (C.D.pt (C.ψ st.1.1.1.1)) + C.rest st.1.1.1.1 (C.aM m) := by
    intro u
    show (Slf.plus (p.G₂.onMem ⟨C.nW, p.kW⟩ p.hW₂ _) fun st => p.restG st.1.1.1.1).val st _ = _
    rw [Slf.plus_val, ldForm_onMem, ldForm_push, ← hr]
    rfl
  have hdot : ∀ u : Unit, (p.sl₂ (.inr u)).val st (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) =
      (∑ y, C.g st.1.1.1.1 y * C.oM m y) - Alg.mle (C.wM m) (C.D.pt st.1.1.2) := by
    intro u
    show (Slf.sub (p.G₂.onMem ⟨C.nO, p.kO⟩ p.hO₂ _) (p.G₂.onMem ⟨C.nW, p.kW⟩ p.hW₂ _)).val st _ = _
    rw [ldForm_sub, ldForm_onMem, ldForm_onMem, ldForm_push, ldForm_push]
    rfl
  constructor
  · intro h
    exact ⟨(hev ()).symm.trans (h (.inl ())), sub_eq_zero.1 ((hdot ()).symm.trans (h (.inr ())))⟩
  · rintro ⟨h1, h2⟩ (u | u)
    · exact (hev u).trans h1
    · exact (hdot u).trans (sub_eq_zero.2 h2)

omit [Fintype ι] in
theorem ldLinPlan_says : Spec.ldLinPlan_says E ι κ J Y := by
  intro C p St' B' fa hr hA
  refine ⟨fun st y m wp h hab => ?_, fun st y m wp hon h => ?_, fun st y hon => hA.on _ y hon⟩
  · exact ⟨(ldLinPlan_rows₁ E ι κ J Y C p st m).2 ⟨h.1, h.2.1, h.2.2.1⟩,
      (ldLinPlan_rows₂ E ι κ J Y C p st m (hr _ m)).2 ⟨h.2.2.2.1, h.2.2.2.2⟩,
      hA.fwd _ y m wp hab⟩
  · obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨a1, a2, a3⟩ := (ldLinPlan_rows₁ E ι κ J Y C p st m).1 h1
    obtain ⟨b1, b2⟩ := (ldLinPlan_rows₂ E ι κ J Y C p st m (hr _ m)).1 h2
    exact ⟨⟨a1, a2, a3, b1, b2⟩, hA.bwd _ y m wp hon h3⟩

end
end Cb
