-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldCodeProofs.lean: the proofs of the statements of Cb/Ld/LdBldCode.lean, the builder of
codes over p = 2^64 - 2^32 + 1 for variable numbers.

Main names (statements and hypotheses: Cb/Ld/LdBldCode.lean):
  `bld_rs_glC`, `bld_cp_glC`, `bld_rep_glC`: `GlC` of the three forms of a row.
  `bld_rs_glJ`, `bld_rs_glS`, `bld_cp_glJ`, `bld_rep_glJ`: `GlJ` of the three forms and of a proper
    subcode.
  `bld_in_glC`, `bld_in_glJ`: `GlC`, `GlJ` of a fold's input code.
  `bld_dist_eq`: two formulas for one distance. `bld_john`: the Johnson condition with the number of
    long positions written as 2^a.
  `bld_rs_read`, `bld_rep_read`, `bld_cp_read`: the long symbols of an honest encoding.
  `bld_card_rs` to `bld_card_out`: the numbers of coordinates of message and randomness.

Each statement on `GlC`, `GlJ` of one of the three forms of a row is proved from one leaf of the
closure. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs.
Limits: what the head of Cb/Ld/LdBldCode.lean lists as not said is not said here either.
-/
import Cb.Ld.LdBldCode
import Cb.Gl.GlLdJProofs
import Cb.Gl.GlCopyProofs
import Code.Facts

set_option autoImplicit false

namespace Cb.Gl.Bld
open Code Prob Blocks

theorem bld_dist_eq : Spec.bld_dist_eq := by
  intro a' a k h
  rw [Nat.mul_sub, ← pow_add, Nat.sub_add_cancel h]

theorem bld_pow_div {a' a : ℕ} (h : a' ≤ a) : 2 ^ a / 2 ^ a' = 2 ^ (a - a') :=
  Nat.pow_div h (by norm_num)

/-! ### GlC -/

theorem bld_rs_glC : Spec.bld_rs_glC := fun a k msg r R _ _ d t ha hk hp hd ht =>
  glC_mono _ _ _ _ d t (.base (gl_code_one a k msg r R ha hk hp)) hd ht

theorem bld_cp_glC : Spec.bld_cp_glC := fun a' a k msg r R fR dR d t hab ha hk hp hd ht =>
  .copy ⟨Unit, inferInstance, inferInstance, fun _ => a', fun _ => a, fun _ => k, fun _ => msg,
    fun _ => r, fun _ x => x, fun _ => 1, fun _ => R, fun _ => fR, fun _ => dR, rfl, fun _ => hab,
    fun _ => ha, fun _ => hk, fun _ => hp, one_even F (rsCp a' a k msg r),
    fun _ => by rw [Nat.one_mul]; exact hd, fun _ => ht⟩

theorem bld_rep_glC : Spec.bld_rep_glC := fun a' a k msg r h R _ _ d t ha hk hp hd ht =>
  .base (gl_code_rep Unit (fun _ => a') (fun _ => k) (fun _ => msg) (fun _ => r) a (fun _ => h)
    (fun _ => R) d t (fun _ => ha) (fun _ => hk) (fun _ => hp)
    (fun _ => by rw [bld_pow_div h]; exact hd) fun _ => ht)

/-! ### GlJ -/

theorem bld_rs_glJ :
    Spec.bld_rs_glJ := fun a k msg r R fR dR d t e bad ha hk0 hk hp hd ht he  hb =>
  .base ⟨Unit, inferInstance, inferInstance, fun _ => a, fun _ => k, fun _ => msg, fun _ => r,
    fun _ x => x, fun _ => 1, fun _ => R, fun _ => fR, fun _ => dR, rfl, fun _ => ha, fun _ => hk0,
    fun _ => hk, fun _ => hp,
    one_even F (rs a k msg r 0 0),
    fun _ => by rw [Nat.one_mul]; exact hd, fun _ => ht, fun _ => he,  by
      simp only [Finset.univ_unique, Finset.sum_singleton, Nat.div_one]
      exact hb⟩

theorem bld_rs_glS :
    Spec.bld_rs_glS := fun a k msg r R fR dR d t e bad ha hk0 hk hp hd ht he  hb =>
  .sub ⟨Unit, inferInstance, inferInstance, fun _ => a, fun _ => k, fun _ => msg, fun _ => r,
    fun _ x => x, fun _ => 1, fun _ => R, fun _ => fR, fun _ => dR, rfl, fun _ => ha, fun _ => hk0,
    fun _ => hk, fun _ => hp,
    one_even F (rs a k msg r 0 0),
    fun _ => by rw [Nat.one_mul]; exact hd, fun _ => ht, fun _ => he,  by
      simp only [Finset.univ_unique, Finset.sum_singleton, Nat.div_one, Fintype.card_fin]
      exact hb⟩

theorem bld_cp_glJ :
    Spec.bld_cp_glJ := fun a' a k msg r R fR dR d t e bad hab ha hk0 hk hp hd ht he  hb =>
  .copy ⟨Unit, inferInstance, inferInstance, fun _ => a', fun _ => a, fun _ => k, fun _ => msg,
    fun _ => r, fun _ x => x, fun _ => 1, fun _ => R, fun _ => fR, fun _ => dR, rfl, fun _ => hab,
    fun _ => ha, fun _ => hk0, fun _ => hk, fun _ => hp,
    one_even F (rsCp a' a k msg r),
    fun _ => by rw [Nat.one_mul]; exact hd, fun _ => ht, fun _ => he,  by
      simp only [Finset.univ_unique, Finset.sum_singleton, Nat.div_one, Fintype.card_fin]
      exact hb⟩

theorem bld_rep_glJ :
    Spec.bld_rep_glJ := fun a' a k msg r h R fR dR d t e bad ha hk0 hk hp hd ht he  hb =>
  .base ⟨Unit, inferInstance, inferInstance, fun _ => a', fun _ => k, fun _ => msg, fun _ => r,
    (Reading.rep (grp (fun _ : Unit => a') (fun _ => k) (fun _ => msg) fun _ => r)
      (2 ^ a) fun _ => pow_dvd_pow 2 h).pos,
    fun _ => 2 ^ a / 2 ^ a', fun _ => R, fun _ => fR, fun _ => dR, rfl,
    fun _ =>
      ha, fun _ =>
          hk0, fun _ =>
              hk, fun _ =>
                  hp, gl_rep_even Unit (fun _ => a') (fun _ => k) (fun _ => msg)
                      (fun _ => r) a fun _ => h,
    fun _ => by rw [bld_pow_div h]; exact hd, fun _ => ht, fun _ => by rw [bld_pow_div h]; exact he,  by
      simp only [Finset.univ_unique, Finset.sum_singleton, bld_pow_div h]
      exact hb⟩

/-! ### A fold's input code -/

theorem bld_in_glC : Spec.bld_in_glC := fun _ _ _ _ _ _ _ _ hC hZ => .pair (.il _ hC) (.il _ hZ)

theorem bld_in_glJ : Spec.bld_in_glJ := fun _ _ _ _ _ _ _ _ _ _ _ hC hZ =>
  .pair (.il _ hC) (.il _ hZ)

theorem bld_john : Spec.bld_john := fun a d e => by rw [Fintype.card_fin]

/-! ### What the codes are -/

/-- the encoder of the plain code, as a polynomial's value
(not all hypotheses are named here: see the statement below) -/
theorem bld_enc_poly (a k msg r : ℕ) (hp : msg + r ≤ k + 1) (m : Fin msg → E)
    (ρ : Fin r → E) (x : Fin (2 ^ a)) :
    (rs a k msg r 0 0).encE E m ρ x = polyAt (algebraMap F E (pts a x)) m ρ := by
  have hs : (rs a k msg r 0 0).fm m ρ = (rs a k msg r 0 0).fm m 0 + (rs a k msg r 0 0).fm 0 ρ := by
    have h := (rs a k msg r 0 0).fm_add m 0 0 ρ
    rwa [add_zero, zero_add] at h
  have h1 := (rs a k msg r 0 0).sum_mul_fm_msg hp (fun i => algebraMap F E (pts a x) ^ (i : ℕ)) m
  have h2 := (rs a k msg r 0 0).sum_mul_fm_rand hp (fun i => algebraMap F E (pts a x) ^ (i : ℕ)) ρ
  show ∑ i : Fin (k + 1), algebraMap F E (pts a x ^ (i : ℕ)) * (rs a k msg r 0 0).fm m ρ i = _
  rw [hs]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_pow]
  exact congrArg₂ (· + ·) h1 h2

theorem bld_rs_read : Spec.bld_rs_read := fun a k msg r _ _ _ hp m ρ x i =>
  bld_enc_poly a k msg r hp (fun j => m ⟨(), (i, j)⟩) (fun q => ρ ⟨(), (i, q)⟩) x

theorem bld_rep_read : Spec.bld_rep_read := fun a' a k msg r _ _ _ _ hp m ρ x i =>
  bld_enc_poly a' k msg r hp (fun j => m ⟨(), (i, j)⟩) (fun q => ρ ⟨(), (i, q)⟩) (cpDn a' a x)

theorem bld_cp_read : Spec.bld_cp_read := fun a' a k msg r h _ _ _ ha m ρ x α =>
  glCp_enc a' a k msg r h ha (fun j => m ⟨α.1, (α.2.1, j)⟩) (fun q => ρ ⟨α.1, (α.2.1, q)⟩) x

/-! ### Numbers of coordinates -/

theorem bld_card_sg (R : Type) [Fintype R] (n : ℕ) :
    Fintype.card (Σ _ : Unit, R × Fin n) = Fintype.card R * n := by
  rw [Fintype.card_congr (sgU (R × Fin n)).symm, Fintype.card_prod, Fintype.card_fin]

theorem bld_card_rs : Spec.bld_card_rs := fun _ _ msg r R _ _ =>
  ⟨bld_card_sg R msg, bld_card_sg R r⟩
theorem bld_card_cp : Spec.bld_card_cp := fun _ _ _ msg r R _ _ =>
  ⟨bld_card_sg R msg, bld_card_sg R r⟩
theorem bld_card_rep : Spec.bld_card_rep := fun _ _ _ msg r _ R _ _ =>
  ⟨bld_card_sg R msg, bld_card_sg R r⟩

theorem bld_card_il : Spec.bld_card_il := fun _ C R _ _ =>
  ⟨Fintype.card_prod R C.J, Fintype.card_prod R C.Q⟩

theorem bld_card_pair : Spec.bld_card_pair := fun _ C₁ C₂ =>
  ⟨Fintype.card_sum (α := C₁.J) (β := C₂.J), Fintype.card_sum (α := C₁.Q) (β := C₂.Q)⟩

theorem bld_card_cube (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem bld_card_in : Spec.bld_card_in := fun P C Z kk h => by
  have h1 := bld_card_pair P (C.il (Fin kk → Bool)) (Z.il (Fin h → Bool))
  have h2 := bld_card_il P C (Fin kk → Bool)
  have h3 := bld_card_il P Z (Fin h → Bool)
  rw [bld_card_cube] at h2 h3
  exact ⟨by rw [h1.1, h2.1, h3.1], by rw [h1.2, h2.2, h3.2]⟩

theorem bld_card_out : Spec.bld_card_out := fun P Y => by
  have h1 := bld_card_pair P Y.C (Y.Z.pair Y.Zw)
  have h2 := bld_card_pair P Y.Z Y.Zw
  refine ⟨?_, ?_⟩
  · rw [h1.1, h2.1, two_mul]
  · rw [h1.2, h2.2, two_mul]

end Cb.Gl.Bld
