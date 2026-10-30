-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPutProofs.lean: the proofs of the statements of Cb/Ld/LdLkpMaskPut.lean.
-/
import Cb.Ld.LdLkpMaskPut

set_option autoImplicit false

namespace Cb
open Iop IOR Prob Hiop

theorem mjPl_reJ : Spec.mjPl_reJ := by
  intro E J J' Xi Xo Ei Eo R D P e h
  refine ⟨⟨fun a b hab => h.inj (e.injective hab), fun M k => funext fun j => ?_⟩, fun j => ⟨fun ⟨i, hi⟩ => ⟨i, by
    have hi' : e (P.pl i) = j := hi
    rw [← hi', e.symm_apply_apply]⟩, fun ⟨i, hi⟩ => ⟨i, ?_⟩⟩⟩
  · show D.put M (fun j' => k (e j')) (e.symm j) =
      Function.extend (fun i => e (P.pl i)) (P.ve M) k j
    rw [h.put]
    by_cases hj : ∃ i, P.pl i = e.symm j
    · obtain ⟨i, hi⟩ := hj
      have hi' : e (P.pl i) = j := by rw [hi, e.apply_symm_apply]
      rw [← hi, h.inj.extend_apply, ← hi']
      exact ((show Function.Injective fun i =>
          e (P.pl i) from fun a b hab => h.inj (e.injective hab)).extend_apply
        _ _ i).symm
    · rw [Function.extend_apply' _ _ _ hj,
        Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => hj ⟨i, by rw [← hi, e.symm_apply_apply]⟩),
        e.apply_symm_apply]
  · show e (P.pl i) = j
    rw [hi, e.apply_symm_apply]

theorem mjPl_post : Spec.mjPl_post := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨⟨h.inj, h.put⟩, fun _ => Iff.rfl⟩
theorem mjPl_pre : Spec.mjPl_pre := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨⟨h.inj, h.put⟩, fun _ => Iff.rfl⟩
theorem mjPl_narrow : Spec.mjPl_narrow := fun _ _ _ _ _ _ _ _ _ _ h =>
  ⟨⟨h.inj, h.put⟩, fun _ => Iff.rfl⟩

theorem mjPl_silent : Spec.mjPl_silent := fun _ _ _ _ _ _ _ _ _ _ =>
  ⟨⟨fun a => a.elim,
      fun _ _ => funext fun _ => (Function.extend_apply' _ _ _ fun ⟨i, _⟩ => i.elim).symm⟩,
    fun _ ⟨i, _⟩ => i.elim⟩

theorem mjPl_at_seq : Spec.mjPl_at_seq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun ⟨i, hi⟩ => i.casesOn (fun a h => Or.inl ⟨a, h⟩) (fun a h => Or.inr ⟨a, h⟩) hi,
    fun h => h.elim (fun ⟨a, h⟩ => ⟨.inl a, h⟩) fun ⟨a, h⟩ => ⟨.inr a, h⟩⟩

theorem mjPl_seq : Spec.mjPl_seq := by
  intro E J X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ D₁ D₂ P₁ P₂ h₁ h₂ hd
  have hinj : Function.Injective (Sum.elim P₁.pl P₂.pl) := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (h₁.inj hab)
    · exact absurd ⟨b, rfl⟩ (hd _ ⟨a, hab⟩)
    · exact absurd ⟨a, rfl⟩ (hd _ ⟨b, hab.symm⟩)
    · exact congrArg Sum.inr (h₂.inj hab)
  refine ⟨hinj, fun M k => funext fun j => ?_⟩
  show D₂.put M.2 (D₁.put M.1 k) j =
    Function.extend (Sum.elim P₁.pl P₂.pl) (Sum.elim (P₁.ve M.1) (P₂.ve M.2)) k j
  rw [h₂.put, h₁.put]
  by_cases h2 : ∃ i, P₂.pl i = j
  · obtain ⟨i, rfl⟩ := h2
    rw [h₂.inj.extend_apply]
    exact (hinj.extend_apply (Sum.elim (P₁.ve M.1) (P₂.ve M.2)) k (Sum.inr i)).symm
  · rw [Function.extend_apply' _ _ _ h2]
    by_cases h1 : ∃ i, P₁.pl i = j
    · obtain ⟨i, rfl⟩ := h1
      rw [h₁.inj.extend_apply]
      exact (hinj.extend_apply (Sum.elim (P₁.ve M.1) (P₂.ve M.2)) k (Sum.inl i)).symm
    · rw [Function.extend_apply' _ _ _ h1, Function.extend_apply' _ _ _ ?_]
      rintro ⟨a | a, ha⟩
      · exact h1 ⟨a, ha⟩
      · exact h2 ⟨a, ha⟩

theorem mjPl_at_chain : Spec.mjPl_at_chain := by
  intro E J K M Ex Wp X b D P n j
  induction n with
  | zero =>
    exact ⟨fun h => ⟨0, le_refl _, h⟩, fun ⟨l, hl, h⟩ => by obtain rfl := Nat.le_zero.1 hl; exact h⟩
  | succ n ih =>
      refine (mjPl_at_seq E J _ _ _ _ _ _ _ _ _ _ (MJ.Pl.chain X b D P n) (P (n + 1)) j).trans ?_
      rw [ih]
      constructor
      · rintro (⟨l, hl, h⟩ | h)
        · exact ⟨l, Nat.le_succ_of_le hl, h⟩
        · exact ⟨n + 1, le_refl _, h⟩
      · rintro ⟨l, hl, h⟩
        rcases Nat.lt_or_ge l (n + 1) with h1 | h1
        · exact Or.inl ⟨l, Nat.lt_succ_iff.1 h1, h⟩
        · obtain rfl := Nat.le_antisymm hl h1
          exact Or.inr h

theorem mjPl_chain : Spec.mjPl_chain := by
  intro E J K M Ex Wp X b D P n
  induction n with
  | zero => exact fun h _ => h 0 (le_refl _)
  | succ n ih =>
      intro h hd
      refine mjPl_seq E J _ _ _ _ _ _ _ _ _ _ (MJ.Pl.chain X b D P n) (P (n + 1))
        (ih (fun l hl => h l (Nat.le_succ_of_le hl)) fun l l' hll hl' =>
          hd l l' hll (Nat.le_succ_of_le hl'))
        (h (n + 1) (le_refl _)) fun j hj => ?_
      obtain ⟨l, hl, hj⟩ := (mjPl_at_chain E J K M Ex Wp X b D P n j).1 hj
      exact hd l (n + 1) (Nat.lt_succ_of_le hl) (le_refl _) j hj

theorem mjPl_writes : Spec.mjPl_writes := fun _ _ _ _ _ _ _ _ _ h M k j hj => by
  rw [h.put, Function.extend_apply' _ _ _ hj]

theorem mjPl_over : Spec.mjPl_over := by
  intro E J Xi Xo Ei Eo R D P h M M' k
  rw [h.put, h.put, h.put]
  funext j
  by_cases hj : ∃ i, P.pl i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [h.inj.extend_apply, h.inj.extend_apply]
  · rw [Function.extend_apply' _ _ _ hj,
      Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj]

section
variable (E : Type) [Field E] [Fintype E]

theorem mjPl_psc : Spec.mjPl_psc E := fun _ _ _ hi =>
  ⟨⟨hi, fun _ _ => rfl⟩, fun _ => ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩⟩

theorem mjPl_our : Spec.mjPl_our E := by
  intro T Ex J e Rd hi
  obtain ⟨h1, h2⟩ := mjPl_psc E T.par Ex (T.own fun j' => Rd (e j')) hi
  obtain ⟨h3, h4⟩ := mjPl_reJ E J T.J _ _ _ _ _ _ (T.par.plOf Ex (T.own fun j' => Rd (e j'))) e h1
  refine ⟨h3, fun j => (h4 j).trans ((h2 _).trans ⟨fun ⟨i, h⟩ => ⟨i, ?_⟩, fun ⟨i, h⟩ => ⟨i, ?_⟩⟩)⟩
  · rw [← e.apply_symm_apply j, h]
    rfl
  · rw [h, e.symm_apply_apply]
    rfl

end
end Cb
