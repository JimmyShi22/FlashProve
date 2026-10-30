-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfTwoProofs.lean: the proofs of Cb/Ld/LdBldWfTwo.lean's two statements. What is said and
what is not: the head of Cb/Ld/LdBldWfTwo.lean.

Main names (statements and hypotheses: Cb/Ld/LdBldWfTwo.lean):
  `bldWf2_injM` (stated here), under `ha` (a₁ ≠ a₂): the placing of the masks is injective (two
    members; two embeddings).
  `bldWf2_room`: a₁ ≠ a₂; pos, adm, zOK, describes ⇒ `T.X.Room p`. `bldWf2_where`: which message
    holds what.
-/
import Cb.Ld.LdBldWfTwo
import Cb.Ld.LdBldMsgProofs
import Cb.Ld.LdBldWfPlace

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E] (T : BldWf2 F E)

theorem bldWf2_pM_last (s : Σ f : T.num.Fo, T.num.LkM E f.1) (h : T.num.Last E s) :
    T.pM (Sum.inl s) = ⟨T.a₂, T.e2 (Sum.inl ⟨s, h⟩)⟩ := dif_pos h
theorem bldWf2_pM_not (s : Σ f : T.num.Fo, T.num.LkM E f.1) (h : ¬ T.num.Last E s) :
    T.pM (Sum.inl s) = ⟨T.a₁, T.e1 ⟨s, h⟩⟩ := dif_neg h

theorem bldWf2_injM (ha : T.a₁ ≠ T.a₂) : Function.Injective T.pM := by
  intro x y e
  cases x with
  | inl s =>
    cases y with
    | inl s' =>
      by_cases h : T.num.Last E s <;> by_cases h' : T.num.Last E s'
      · rw [bldWf2_pM_last T s h, bldWf2_pM_last T s' h'] at e
        have e2 := Sum.inl.inj (T.e2.injective (eq_of_heq (Sigma.mk.inj_iff.1 e).2))
        exact congrArg Sum.inl (congrArg Subtype.val e2)
      · rw [bldWf2_pM_last T s h, bldWf2_pM_not T s' h'] at e
        exact absurd (Sigma.mk.inj_iff.1 e).1.symm ha
      · rw [bldWf2_pM_not T s h, bldWf2_pM_last T s' h'] at e
        exact absurd (Sigma.mk.inj_iff.1 e).1 ha
      · rw [bldWf2_pM_not T s h, bldWf2_pM_not T s' h'] at e
        exact congrArg Sum.inl
          (congrArg Subtype.val (T.e1.injective (eq_of_heq (Sigma.mk.inj_iff.1 e).2)))
    | inr i =>
      by_cases h : T.num.Last E s
      · rw [bldWf2_pM_last T s h] at e
        have e' : (⟨T.a₂, T.e2 (Sum.inl ⟨s, h⟩)⟩ : Σ a, T.Fm.lay.Fr a) = ⟨T.a₂, T.e2 (Sum.inr i)⟩ :=
          e
        cases T.e2.injective (eq_of_heq (Sigma.mk.inj_iff.1 e').2)
      · rw [bldWf2_pM_not T s h] at e
        have e' : (⟨T.a₁, T.e1 ⟨s, h⟩⟩ : Σ a, T.Fm.lay.Fr a) = ⟨T.a₂, T.e2 (Sum.inr i)⟩ := e
        exact absurd (Sigma.mk.inj_iff.1 e').1 ha
  | inr i =>
    cases y with
    | inl s' =>
      by_cases h' : T.num.Last E s'
      · rw [bldWf2_pM_last T s' h'] at e
        have e' : (⟨T.a₂, T.e2 (Sum.inr i)⟩ : Σ a, T.Fm.lay.Fr a) =
            ⟨T.a₂, T.e2 (Sum.inl ⟨s', h'⟩)⟩ := e
        cases T.e2.injective (eq_of_heq (Sigma.mk.inj_iff.1 e').2)
      · rw [bldWf2_pM_not T s' h'] at e
        have e' : (⟨T.a₂, T.e2 (Sum.inr i)⟩ : Σ a, T.Fm.lay.Fr a) = ⟨T.a₁, T.e1 ⟨s', h'⟩⟩ := e
        exact absurd (Sigma.mk.inj_iff.1 e').1.symm ha
    | inr i' =>
      have e' : (⟨T.a₂, T.e2 (Sum.inr i)⟩ : Σ a, T.Fm.lay.Fr a) = ⟨T.a₂, T.e2 (Sum.inr i')⟩ := e
      exact congrArg Sum.inr (Sum.inr.inj (T.e2.injective (eq_of_heq (Sigma.mk.inj_iff.1 e').2)))

end

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

theorem bldWf2_room : Spec.bldWf2_room F E := fun T p ha hpos hadm hZ hD =>
  { pos := hpos
    adm := hadm
    injB := fun a b e => T.eB.injective (eq_of_heq (Sigma.mk.inj_iff.1 e).2)
    injM := bldWf2_injM T ha
    zOK := hZ
    fair := (bld_fair E T.Fm).1
    supR := fun f hf _ => ⟨trivial, fun _ _ => trivial, fun a ha' => by
      rw [T.X.mkN_pos f hf]
      exact fun ⟨h, c, e⟩ => ha' h c e⟩
    describes := hD }

theorem bldWf2_where : Spec.bldWf2_where F E := by
  intro T
  refine ⟨fun _ _ n hn => ?_, fun f hf n hn => ?_, fun _ => rfl⟩
  · cases n with
    | inl b => rfl
    | inr m =>
      cases m with
      | inl s => exact congrArg Sigma.fst (bldWf2_pM_not T s hn)
      | inr i => exact hn.elim
  · obtain ⟨c, rfl⟩ := ((bldWf_where F E E T.X f hf).1 n).1 hn
    rw [T.X.mkN_pos f hf]
    exact congrArg Sigma.fst
      (bldWf2_pM_last T ⟨⟨f, hf⟩, .k (T.num.v' f) (le_refl _) (Sum.inr c)⟩ ⟨le_refl _, c, rfl⟩)

end
end Cb
