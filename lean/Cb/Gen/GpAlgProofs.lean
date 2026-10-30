-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/GpAlgProofs.lean: the statements of Cb/Gen/GpAlg.lean, proved.
-/
import Cb.Gen.GpAlg

set_option autoImplicit false

namespace Cb
open Blocks Finset Prob Cb.Gp

theorem rel_iff_zero : Spec.rel_iff_zero := by
  intro E _ g n A h
  refine forall_congr' fun θ => forall_congr' fun _ => ?_
  rw [lvl_zero, sub_eq_zero]

theorem zero_iff_claim0 : Spec.zero_iff_claim0 := by
  intro E _ g n A h z
  unfold Claim
  rw [ext_sub, sub_eq_zero, Nat.zero_add]

theorem claim_iff_sum : Spec.claim_iff_sum := by
  intro E _ g n A l z t hl
  unfold Claim Blocks.ext up
  have : ∀ X, lvl g n A l X = lvl g n A (l + 1) X * lvl g n A (l + 1) (X + 2 ^ (l + g)) := fun X =>
    lvl_step g n A hl X
  simp only [this]

theorem line_defect : Spec.line_defect := by
  intro E _ k f r c v₀ v₁
  rw [ext_succ_consPt]
  unfold up
  ring

theorem cnt_line_le_one : Spec.cnt_line_le_one := by
  intro E _ _ k f r v₀ v₁ h
  have hab : (ext k f r - v₀) ≠ 0 ∨ ((ext k (up k f) r - v₁) - (ext k f r - v₀)) ≠ 0 := by
    by_cases h0 : ext k f r - v₀ = 0
    · right
      rw [h0, sub_zero]
      exact sub_ne_zero.2 (h.resolve_left fun hn => hn (sub_eq_zero.1 h0))
    · exact Or.inl h0
  refine le_trans (cnt_mono fun c hc => ?_) (Alg.count_affine_le_one _ _ hab)
  have hd := line_defect E k f r c v₀ v₁
  rw [hc, sub_self] at hd
  linear_combination -hd

theorem line_claim : Spec.line_claim := by
  intro E _ g n A l r c t
  unfold Claim
  rw [show l + 1 + g = l + g + 1 by omega]

theorem claim_top : Spec.claim_top := by
  intro E _ g n A z t
  unfold Claim
  rw [lvl_top]

end Cb
