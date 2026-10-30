-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`IsGlJ`, `IsGlS` (Cb/Gl/GlLdJ.lean) and `IsGlCpJ` (Cb/Gl/GlCopy.lean) do not ask a radius within
half the distance.
Cb/Ld/LdBldCodeAtProofs.lean: the proofs of Cb/Ld/LdBldCodeAt.lean: `GlJ` along a reading at other
positions. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold
as proofs.

Main names (statements and hypotheses: Cb/Ld/LdBldCodeAt.lean):
  `bld_card_atPos`: the number of new positions.
  `bld_listMax_mul`, `bld_john_mul`: the Johnson bound on the list and the Johnson condition under a
    factor m.
  `bld_isGlJ_atPos`, `bld_isGlS_atPos`, `bld_isGlCpJ_atPos`: the three kinds of leaves.
  `bld_glJ_atPos`: the closure `GlJ`.

Limits: what the head of Cb/Ld/LdBldCodeAt.lean lists as not said is not said here either.
-/
import Cb.Ld.LdBldCodeAt
import Cb.Gl.GlLdJProofs

set_option autoImplicit false

namespace Cb.Gl.Bld
open Code Prob Blocks

theorem bld_card_atPos : Spec.bld_card_atPos := by
  intro P P' _ _ pos' m h
  classical
  have e := CodeRep.cnt_comp_even pos' m h fun _ => True
  rw [cnt_eq_card_filter, cnt_eq_card_filter] at e
  simpa using e

/-- the two terms of the Johnson condition, multiplied -/
theorem bld_john_terms (m n d e : ℕ) :
    m * n * (m * n - m * d) = m ^ 2 * (n * (n - d)) ∧
    (m * n - m * e) ^ 2 = m ^ 2 * (n - e) ^ 2 := by
  rw [← Nat.mul_sub, ← Nat.mul_sub]
  exact ⟨by ring, by ring⟩

theorem bld_listMax_mul : Spec.bld_listMax_mul := by
  intro m n d e hm
  unfold listMax
  rw [(bld_john_terms m n d e).1, (bld_john_terms m n d e).2, ← Nat.mul_sub, ← Nat.mul_sub]
  have e1 : m * n * (m * (d - e)) = m ^ 2 * (n * (d - e)) := by ring
  rw [e1]
  exact Nat.mul_div_mul_left _ _ (pow_pos hm 2)

theorem bld_john_mul : Spec.bld_john_mul := by
  intro m n d e hm
  unfold InJohnson
  rw [(bld_john_terms m n d e).1, (bld_john_terms m n d e).2]
  exact Nat.mul_lt_mul_left (pow_pos hm 2)

theorem bld_isGlJ_atPos : Spec.bld_isGlJ_atPos := by
  rintro P P' _ _ C d t e bad pos' m
    ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk0, hk, hp, hE, hd, ht, hm', hb⟩
    hm hpos
  refine ⟨A, iA, dA, a, k, msg, r, fun i x => pos i (pos' x), fun i => m * mult i, R, fR, dR, rfl,
    ha, hk0, hk, hp, fun i => ⟨Nat.mul_pos hm (hE i).1, fun y => ?_⟩, fun i => ?_, ht,
    fun i => Nat.mul_le_mul_left m (hm' i),  ?_⟩
  · have e := CodeRep.cnt_comp_even pos' m hpos fun z => pos i z = y
    exact e.trans (congrArg (m * ·) ((hE i).2 y))
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left m (hd i)
  · simp only [Nat.mul_div_mul_left _ _ hm]
    exact hb

theorem bld_isGlS_atPos : Spec.bld_isGlS_atPos := by
  rintro P P' _ _ C d t e bad pos' m
    ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk0, hk, hp, hE, hd, ht, hm', hb⟩
    hm hpos
  refine ⟨A, iA, dA, a, k, msg, r, fun i x => pos i (pos' x), fun i => m * mult i, R, fR, dR, rfl,
    ha, hk0, hk, hp, fun i => ⟨Nat.mul_pos hm (hE i).1, fun y => ?_⟩, fun i => ?_, ht,
    fun i => Nat.mul_le_mul_left m (hm' i),  ?_⟩
  · have e := CodeRep.cnt_comp_even pos' m hpos fun z => pos i z = y
    exact e.trans (congrArg (m * ·) ((hE i).2 y))
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left m (hd i)
  · rw [bld_card_atPos P P' pos' m hpos, bld_listMax_mul m _ d e hm]
    simp only [Nat.mul_div_mul_left _ _ hm]
    exact hb

theorem bld_isGlCpJ_atPos : Spec.bld_isGlCpJ_atPos := by
  rintro P P' _ _ C d t e bad pos' m
    ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, rfl, hab, hb32, hk0, hk,
      hp, hE, hd, ht, hm', hb⟩
    hm hpos
  refine ⟨A, iA, dA, a, b, k, msg, r, fun i x => pos i (pos' x), fun i => m * mult i, R, fR, dR,
    rfl, hab, hb32, hk0, hk, hp, fun i => ⟨Nat.mul_pos hm (hE i).1, fun y => ?_⟩, fun i => ?_, ht,
    fun i => Nat.mul_le_mul_left m (hm' i),  ?_⟩
  · have e := CodeRep.cnt_comp_even pos' m hpos fun z => pos i z = y
    exact e.trans (congrArg (m * ·) ((hE i).2 y))
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left m (hd i)
  · rw [bld_card_atPos P P' pos' m hpos, bld_listMax_mul m _ d e hm]
    simp only [Nat.mul_div_mul_left _ _ hm]
    exact hb

theorem bld_glJ_atPos : Spec.bld_glJ_atPos := by
  intro P P' _ _ C d t e bad pos' m h hm hpos
  induction h with
  | base h => exact .base (bld_isGlJ_atPos P P' _ _ _ _ _ pos' m h hm hpos)
  | sub h => exact .sub (bld_isGlS_atPos P P' _ _ _ _ _ pos' m h hm hpos)
  | copy h => exact .copy (bld_isGlCpJ_atPos P P' _ _ _ _ _ pos' m h hm hpos)
  | il R _ ih => exact GlJ.il R ih
  | @pair C₁ C₂ _ _ _ _ _ _ _ ih₁ ih₂ =>
      have e : (C₁.pair C₂).atPos pos' = (C₁.atPos pos').pair (C₂.atPos pos') := by
        show LdCode.mk _ _ _ _ _ _ _ _ = LdCode.mk _ _ _ _ _ _ _ _
        congr 1
        all_goals
          funext f x α
          cases α <;> rfl
      rw [e]
      exact GlJ.pair ih₁ ih₂
  | fam _ ih => exact GlJ.fam ih
  | up _ hb ih => exact GlJ.up ih hb

end Cb.Gl.Bld
