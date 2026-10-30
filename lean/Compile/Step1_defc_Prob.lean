-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_defc_Prob.lean: facts on uniform distributions (β, γ finite and nonempty).

  `unif_eq_bind_fibre`   If χ carries the uniform law of β to the uniform law of γ, then a uniform b
                         is: a uniform c, then b uniform in the fibre of χ over c.
  `unif_prod_map_fst`    The first component of a uniform pair is uniform.
-/
import Prob.Tv

open scoped ENNReal
open Prob

namespace Compile.DefC

variable {β γ : Type} [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ] [DecidableEq γ]

/-- the fibre of χ over c -/
def fibre (χ : β → γ) (c : γ) : Finset β := Finset.univ.filter fun b => χ b = c

theorem card_fibre (χ : β → γ)
    (h : (PMF.uniformOfFintype β).map χ = PMF.uniformOfFintype γ) (c : γ) :
    ((fibre χ c).card : ℝ≥0∞) * (Fintype.card β : ℝ≥0∞)⁻¹ = (Fintype.card γ : ℝ≥0∞)⁻¹ := by
  have h1 := congrArg (fun p : PMF γ => p c) h
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype] at h1
  rw [← h1]
  simp only [fibre, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : χ b = c
  · simp [hb]
  · have : c ≠ χ b := fun e => hb e.symm
    simp [hb, this]

theorem fibre_nonempty (χ : β → γ)
    (h : (PMF.uniformOfFintype β).map χ = PMF.uniformOfFintype γ) (c : γ) :
    (fibre χ c).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h1 := card_fibre χ h c
  rw [hne] at h1
  simp only [Finset.card_empty, Nat.cast_zero, zero_mul] at h1
  exact (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)) h1.symm

theorem unif_eq_bind_fibre (χ : β → γ)
    (h : (PMF.uniformOfFintype β).map χ = PMF.uniformOfFintype γ) :
    PMF.uniformOfFintype β =
      (PMF.uniformOfFintype γ).bind fun c =>
        PMF.uniformOfFinset (fibre χ c) (fibre_nonempty χ h c) := by
  ext b
  rw [PMF.bind_apply, tsum_eq_single (χ b)]
  · have hb : b ∈ fibre χ (χ b) := by simp [fibre]
    rw [PMF.uniformOfFinset_apply_of_mem _ hb, PMF.uniformOfFintype_apply,
      PMF.uniformOfFintype_apply, ← card_fibre χ h (χ b)]
    have hc : ((fibre χ (χ b)).card : ℝ≥0∞) ≠ 0 := by
      simpa using (Finset.card_pos.2 ⟨b, hb⟩).ne'
    rw [mul_comm ((fibre χ (χ b)).card : ℝ≥0∞), mul_assoc,
      ENNReal.mul_inv_cancel hc (by simp), mul_one]
  · intro c hc
    have hb : b ∉ fibre χ c := by simp [fibre, Ne.symm hc]
    rw [PMF.uniformOfFinset_apply_of_notMem _ hb, mul_zero]

omit [DecidableEq γ] in
theorem unif_prod_map_fst :
    (PMF.uniformOfFintype (β × γ)).map Prod.fst = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_eq_single b]
  · simp only [if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.mul_inv (by simp) (by simp), mul_comm (Fintype.card β : ℝ≥0∞)⁻¹, ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  · intro b' _ hb'
    simp [Ne.symm hb']
  · simp

end Compile.DefC
