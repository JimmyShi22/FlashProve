-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelProofs.lean: the proofs of the statements of Cb/Ld/LdRel.lean on the relaxation and on
linear forms (Cb.Spec.ld_con* but for `Spec.ld_conL_two`, ld_slf_*, ld_holds_unfold). Those on
codes, and that of `Spec.ld_conL_two`, are in Cb/Ld/LdRelProofsCode.lean.
-/
import Cb.Ld.LdRel
import Cb.Gen.CodeOnto
import Prob.Count

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

theorem offCnt_self {Ex : ExtSpec} [Finite Ex.Pos] (y : Ex.Str) : offCnt y y = 0 :=
  cnt_false fun _ h => h rfl

theorem ld_conLit_iff : Spec.ld_conLit_iff := by
  intro Ex _ N X e Φ a w y'
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h2 ▸ h1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨h2 ▸ h1, h2, h3⟩

theorem ld_con_sub_conL : Spec.ld_con_sub_conL := by
  intro Ex _ N X e Φ x y w h
  refine ⟨?_, h.2⟩
  show offCnt y (N.enc w.1 w.2) ≤ e
  rw [h.1, offCnt_self]
  exact Nat.zero_le _

theorem ld_conL_mono : Spec.ld_conL_mono := fun _ _ _ _ _ _ _ _ he hΦ _ _ h =>
  ⟨le_trans h.1 he, hΦ _ _ h.2⟩

theorem ld_conL_zero : Spec.ld_conL_zero := by
  intro Ex _ N X Φ hext x y w
  refine ⟨fun h => ⟨hext _ _ fun p => ?_, h.2⟩, fun h => ld_con_sub_conL Ex N X 0 Φ x y w h⟩
  by_contra hne
  have h0 : offCnt y (N.enc w.1 w.2) = 0 := Nat.le_zero.1 h.1
  have : IsEmpty {p : Ex.Pos // Ex.rd y p ≠ Ex.rd (N.enc w.1 w.2) p} := by
    have := (Nat.card_eq_zero.1 h0)
    rcases this with h | h
    · exact h
    · exact absurd (inferInstance : Finite _) (not_finite_iff_infinite.2 h)
  exact this.false ⟨p, hne⟩

theorem ld_conL_guard : Spec.ld_conL_guard := by
  intro F E _ _ _ _ _ c hc hk X Φ a w
  have h := comp_dec_onto F E c hc hk a.2 w.1 w.2
  exact ⟨fun g => ⟨h.2 g.1, g.2⟩, fun g => ⟨h.1 g.1, g.2⟩⟩

section
variable (E : Type) [Field E]

theorem ld_slf_unfold : Spec.ld_slf_unfold E := by
  intro St J ι _ _ _ sl st γ v
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Slf.unfold, foldV, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem ld_holds_unfold : Spec.ld_holds_unfold E := by
  intro St J ι _ _ _ sl τ st γ v
  show (∑ n, sl.unfold (st, γ) n * v n = τ) ↔ (∑ c, sl st c * foldV γ v c = τ)
  rw [ld_slf_unfold E]

theorem ld_slf_fix_corner : Spec.ld_slf_fix_corner E := by
  intro St J ι _ _ sl st b c
  classical
  show ∑ b', sl st (b', c) * Alg.eqk (Alg.corner b) b' = sl st (b, c)
  simp only [Alg.eqk_corner]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ h
    rw [if_neg (Ne.symm h), mul_zero]
  · simp

theorem ld_slf_pair : Spec.ld_slf_pair E := by
  intro St₁ St₂ J₁ J₂ _ _ sl₁ sl₂ x m
  rw [Fintype.sum_sum_type]
  rfl

theorem ld_slf_bat : Spec.ld_slf_bat E := by
  intro J B D _ _ S Z sl x m
  simp only [Slf.bat, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring

end
end Cb
