-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecSendProofs.lean: the proofs of the statements of Cb/Gen/OodDecSend.lean (the number of
bad seeds after the words are sent).

Every theorem here is "name : Cb.Spec.name", three of them at F and E.
-/
import Cb.Gen.OodDecSend
import Cb.Gen.OodDecRepProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

theorem ood_val_comap : Spec.ood_val_comap := by
  intro E J J' _ _ _ Z σ ρ u
  funext s
  show ∑ j', Z.mat ρ s (σ j') * u j' = ∑ j, Z.mat ρ s j * u (σ.symm j)
  exact Fintype.sum_equiv σ _ _ fun j' => by rw [Equiv.symm_apply_apply]

theorem ood_okOn_comap : Spec.ood_okOn_comap := by
  intro E J J' _ _ _ Z σ V hZ u hV hu
  have hne : (fun j => u (σ.symm j)) ≠ 0 := fun h => hu (funext fun j' => by
    have := congrFun h (σ j')
    rwa [Equiv.symm_apply_apply] at this)
  refine (cnt_mono fun ρ hρ => ?_).trans (hZ _ hV hne)
  exact (ood_val_comap E J J' Z σ ρ u).symm.trans hρ

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] [Fintype E] in
theorem ood_cx_padInF : Spec.ood_cx_padInF F E := by
  intro K J₀ P σ hσ m m' i
  obtain ⟨x, hx⟩ := Kf.toE_mem_range
    (hσ i) (m (σ.symm (Sum.inr i)).1 (σ.symm (Sum.inr i)).2.1 (σ.symm (Sum.inr i)).2.2)
  obtain ⟨x', hx'⟩ := Kf.toE_mem_range
    (hσ i) (m' (σ.symm (Sum.inr i)).1 (σ.symm (Sum.inr i)).2.1 (σ.symm (Sum.inr i)).2.2)
  exact ⟨x - x', by rw [map_sub, hx, hx']; rfl⟩

theorem ood_send : Spec.ood_send F E := by
  intro K T D e μ J₀ P B _ _ _ _ _ _ pl w b σ y hp hT hd hD hJ hpl hb hw hσ
  have hZ := ood_okOn_comap E (J₀ ⊕ P) K.Ent (Sample.pad E μ J₀ P B pl w b) σ (PadInF F)
    (ood_okOn_pad F E μ J₀ P B pl w b hpl hb hw)
  have h1 := ood_cxU_johnson F E K T D e ((Sample.pad E μ J₀ P B pl w b).comap σ)
    _ y hp hT hd hD hJ hZ (ood_cx_padInF F E K J₀ P σ hσ)
  have h2 := two_mul_le_sq h1
  have h3 := ood_frac_pad E μ J₀ P B pl w b hb
  calc
    2 * cnt (fun ρ : (μ → E) × B =>
            ∃ v, K.CollU E T e ((Sample.pad E μ J₀ P B pl w b).comap σ) y ρ v) * Fintype.card B ≤
        listMax (Fintype.card T.P) D e ^ 2 * (Sample.pad E μ J₀ P B pl w b).err * Fintype.card B :=
      Nat.mul_le_mul_right _ h2
    _ = listMax (Fintype.card T.P) D e ^ 2 *
          ((Sample.pad E μ J₀ P B pl w b).err * Fintype.card B) :=
      Nat.mul_assoc _ _ _
    _ ≤ listMax (Fintype.card T.P) D e ^ 2 * ((Fintype.card μ + 1) * Fintype.card ((μ → E) × B)) :=
      Nat.mul_le_mul_left _ h3

theorem ood_send_good : Spec.ood_send_good F E := by
  intro K T rank e Z y ρ hs v m
  exact (ood_cxU_good F E K T rank e Z y ρ v fun hc => hs ⟨v, hc⟩).1 m

end
end Cb
