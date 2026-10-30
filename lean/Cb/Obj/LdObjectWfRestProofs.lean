-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectWfRestProofs.lean: the proofs of the statements of Cb/Obj/LdObjectWfRest.lean ("restG
is rest" at the object).
Nothing is defined here that a statement reads.
-/
import Cb.Obj.LdObjectWfRest

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

theorem ldRest_val : Spec.ldRest_val := by
  intro E ι κ J Y _ C p slA hs sa m
  have s1 : ∀ (n : C.S.Ent), ¬ p.kp₁ n.1 → C.upA slA sa n = 0 := by
    rintro ⟨((a | a) | a) | a, j⟩ hn
    · by_contra hne
      exact hn (hs sa a j hne).1
    · rfl
    · rfl
    · rfl
  have s2 : ∀ (n : p.S₁.Ent), ¬ p.G₂.mem n.1 → ((C.upA slA).onSub p.kp₁) sa n = 0 := by
    rintro ⟨⟨((a | a) | a) | a, h⟩, j⟩ hn
    · by_contra hne
      exact hn (hs sa a j hne).2
    · rfl
    · rfl
    · rfl
  exact (ldPeel_onG E p.S₁ p.G₂ C.Sta ((C.upA slA).onSub p.kp₁) sa
      (C.S.res (T := OMsg.Msg) p.kp₁ m) s2).trans
    ((ldPeel_onSub E C.S p.kp₁ C.Sta (C.upA slA) sa m s1).trans (C.upA_val slA sa m))

theorem ldRest_is : Spec.ldRest_is := by
  intro E ι κ J Y _ C p slA hG hr hs sa m
  rw [hG, hr]
  exact ldRest_val E ι κ J Y C p slA hs sa m

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOWfRest_val : Spec.ldOWfRest_val F E := by
  intro W nAt hE cl m
  unfold LdOWf.restF
  rw [Slf.plus_val, ldForm_push, ldForm_push]
  show _ = W.P.bt.maskPart cl (Sum.elim (fun _ => 0) (W.P.ent m))
  unfold BattPar.maskPart
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) ?_
  · rw [← hE.ent]
    rfl
  · have e : ∀ q : Fin (W.P.n + 1), ∑ j,
          W.P.bt.slM q cl.st.1 j * (Sum.elim (fun _ => 0) (W.P.ent m) : W.P.bt.J → E) j =
        ∑ n, (W.P.clAt q (W.P.stOf cl)).mf n * W.P.ent m n := by
      intro q
      show ∑ j : (W.P.Rw × (Fin W.P.k → Bool)) ⊕ W.P.N, _ = _
      rw [Fintype.sum_sum_type]
      have z : ∑ x : W.P.Rw × (Fin W.P.k → Bool), W.P.bt.slM q cl.st.1 (Sum.inl x) *
            (Sum.elim (fun _ => 0) (W.P.ent m) : W.P.bt.J → E) (Sum.inl x) = 0 :=
        Finset.sum_eq_zero fun x _ => mul_zero _
      rw [z, zero_add]
      rfl
    simp only [e]
    simp only [← hE.ent, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun n _ => by ring

theorem ldOWfRest_read : Spec.ldOWfRest_read F E := by
  intro W nAt cl e hne
  by_contra hno
  rw [not_or] at hno
  obtain ⟨h1, h2⟩ := hno
  apply hne
  show Slf.push _ _ cl e + Slf.push _ _ cl e = 0
  rw [Slf.push_zero _ _ cl e fun i hi => h1 ⟨i, hi⟩, zero_add]
  refine Finset.sum_eq_zero fun n _ => ?_
  by_cases hn : nAt n = e
  · rw [if_pos hn]
    have z : ∀ q : Fin (W.P.n + 1), (W.P.clAt q (W.P.stOf cl)).mf n = 0 := fun q =>
      if_neg fun hg => h2 ⟨q, n, hg, hn⟩
    simp only [z, mul_zero, Finset.sum_const_zero]
  · rw [if_neg hn]

theorem ldOWfRest_is : Spec.ldOWfRest_is F E := by
  intro W nAt p hE hG hp1 hp2
  refine ldRest_is E _ _ _ _ W.O.toC p (W.restF nAt) hG
    (fun sa ma => (ldOWfRest_val F E W nAt hE sa ma).symm) fun st a j hne => ?_
  rcases ldOWfRest_read F E W nAt st ⟨a, j⟩ hne with ⟨i, hi⟩ | ⟨q, n, hg, hn⟩
  · have ha := congrArg Sigma.fst hi
    have h := hp1 i
    rw [ha] at h
    exact h
  · have ha : (nAt n).1 = a := congrArg Sigma.fst hn
    subst ha
    exact hp2 q n hg

end
end Cb
