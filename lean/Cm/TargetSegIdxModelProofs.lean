-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegIdxModelProofs.lean: the proofs of the statements of Cm/TargetSegIdxModel.lean (the
weight tensors of the model as index atoms), over p = 2^64 - 2^32 + 1.

The fields are `Cb.Gl.F`, `Cb.Gl.E`
(Cb/Gl/GlField.lean); the format is
`Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean).


The statements and their limits: the head of Cm/TargetSegIdxModel.lean.



-/
import Cm.SegIdxModelProofs
import Cm.TargetSegAll
import Cm.TargetSegIdxModel


set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Blocks Finset Code Inst.Model Inst.Model.Layout

theorem r_ok : Spec.r_ok := fun v n U σs hw hOK => t_ok Cb.Gl.F Cb.Gl.E fmtRef v ppref n U σs hw hOK

theorem r_vtx : Spec.r_vtx := fun v n U σs hU hw W b =>
  t_vtx Cb.Gl.F Cb.Gl.E fmtRef v ppref n U σs hw
    (Tensor.rows_fit kRef hRef (units ppref) n U hU IndexM.total_le) W b

theorem ok2 : Spec.ok2 := fun v n R₁ R₂ nU k₁ k₂ σ₁ σ₂ h₁ h₂ p₁ p₂ l₁ l₂ hOK =>
  r_ok v n _ _ (widths2 h₁ h₂ p₁ p₂ l₁ l₂) (by simpa using hOK)

theorem ok3 : Spec.ok3 := fun v n R₁ R₂ R₃ nU k₁ k₂ k₃ σ₁ σ₂ σ₃ h₁ h₂ h₃ p₁ p₂ p₃ l₁ l₂ l₃ hOK =>
  r_ok v n _ _ (widths3 h₁ h₂ h₃ p₁ p₂ p₃ l₁ l₂ l₃) (by simpa using hOK)

theorem vtx2 : Spec.vtx2 := by
  classical
  intro v n R₁ R₂ nU k₁ k₂ σ₁ σ₂ h₁ h₂ hU p₁ p₂ l₁ l₂ W b
  rw [r_vtx v n _ _ hU (widths2 h₁ h₂ p₁ p₂ l₁ l₂) W b]
  have hiff : InRows [⟨R₁, k₁⟩, ⟨R₂, k₂⟩] kRef (numsAt [σ₁, σ₂] v b) ↔
      (Src.num σ₁ v b < R₁ ∧ Src.num σ₂ v b < R₂) := by
    simp [InRows, numsAt, h₁, h₂]
  unfold FFSeg.matR
  by_cases h : Src.num σ₁ v b < R₁ ∧ Src.num σ₂ v b < R₂
  · rw [if_pos (hiff.2 h), if_pos h]
    rfl
  · rw [if_neg (fun hh => h (hiff.1 hh)), if_neg h, map_zero]

theorem vtx3 : Spec.vtx3 := by
  classical
  intro v n R₁ R₂ R₃ nU k₁ k₂ k₃ σ₁ σ₂ σ₃ h₁ h₂ h₃ hU p₁ p₂ p₃ l₁ l₂ l₃ W b
  rw [r_vtx v n _ _ hU (widths3 h₁ h₂ h₃ p₁ p₂ p₃ l₁ l₂ l₃) W b]
  have hiff : InRows [⟨R₁, k₁⟩, ⟨R₂, k₂⟩, ⟨R₃, k₃⟩] kRef (numsAt [σ₁, σ₂, σ₃] v b) ↔
      (Src.num σ₁ v b < R₁ ∧ Src.num σ₂ v b < R₂ ∧ Src.num σ₃ v b < R₃) := by
    simp [InRows, numsAt, h₁, h₂, h₃]
  unfold FFSeg.matR
  by_cases h : Src.num σ₁ v b < R₁ ∧ Src.num σ₂ v b < R₂ ∧ Src.num σ₃ v b < R₃
  · rw [if_pos (hiff.2 h), if_pos h.2.1, if_pos ⟨h.1, h.2.2⟩]
    rfl
  · rw [if_neg (fun hh => h (hiff.1 hh))]
    by_cases he : Src.num σ₂ v b < R₂
    · rw [if_pos he, if_neg (fun hh => h ⟨hh.1, he, hh.2⟩), map_zero]
    · rw [if_neg he, map_zero]

/-! ### The units of a layer -/

theorem v_vtx : Spec.v_vtx := fun v L σj σx hL hj hx W b =>
  vtx2 v (first ppref L + 1) ppref.d (ppref.nkv * ppref.ch) 2 .low .high σj σx (by decide)
    (by decide) (unitL hL rfl) (by decide) (by decide) hj hx W b

theorem o_vtx : Spec.o_vtx := fun v L σj σx hL hj hx W b =>
  vtx2 v (first ppref L + 2) (ppref.nq * ppref.ch) ppref.d 2 .low .high σj σx (by decide)
    (by decide) (unitL hL rfl) (by decide) (by decide) hj hx W b

theorem g_vtx : Spec.g_vtx := by
  intro v L σj σx hL hj hx W b
  refine (vtx2 v (first ppref L + 3) ppref.d (fOf L) 2 .low .high σj σx (by decide) (by decide)
      (unit_g hL) (by decide) (fOf_pos L) hj hx W b).trans
    (congrArg (algebraMap Cb.Gl.F Cb.Gl.E) ?_)
  show _ = (if hasExperts L then _ else _ : ℕ → ℕ → Cb.Gl.F) _ _
  unfold fOf
  split_ifs <;> rfl

theorem u_vtx : Spec.u_vtx := by
  intro v L σj σx hL hj hx W b
  refine (vtx2 v (first ppref L + 4) ppref.d (fOf L) 2 .low .high σj σx (by decide) (by decide)
      (unit_u hL) (by decide) (fOf_pos L) hj hx W b).trans
    (congrArg (algebraMap Cb.Gl.F Cb.Gl.E) ?_)
  show _ = (if hasExperts L then _ else _ : ℕ → ℕ → Cb.Gl.F) _ _
  unfold fOf
  split_ifs <;> rfl

theorem d_vtx : Spec.d_vtx := by
  intro v L σj σx hL hj hx W b
  refine (vtx2 v (first ppref L + (if hasExperts L then 7 else 5)) (fOf L) ppref.d 2 .low .high σj
      σx (by decide) (by decide) (unit_d hL) (fOf_pos L) (by decide) hj hx W b).trans
    (congrArg (algebraMap Cb.Gl.F Cb.Gl.E) ?_)
  show _ = (if hasExperts L then _ else _ : ℕ → ℕ → Cb.Gl.F) _ _
  unfold fOf
  split_ifs <;> rfl

theorem r_vtx' : Spec.r_vtx' := by
  intro v L σj σe hL hx hj he W b
  refine (vtx2 v (first ppref L + 9) ppref.d ppref.nexp 2 .low .high σj σe (by decide) (by decide)
      (unit_x hL hx rfl) (by decide) (by decide) hj he W b).trans
    (congrArg (algebraMap Cb.Gl.F Cb.Gl.E) ?_)
  show _ = (if hasExperts L then _ else _ : ℕ → ℕ → Cb.Gl.F) _ _
  rw [if_pos hx]
  rfl

theorem routed_eq {L : ℕ} (hx : hasExperts L) (A : ℕ → ℕ → ℕ → Cb.Gl.F) (e j x : ℕ) :
    (if e < ppref.nexp then A e j x else 0) =
      (if hasExperts L ∧ e < ppref.nexp then A e else fun _ _ => 0) j x := by
  by_cases he : e < ppref.nexp
  · rw [if_pos he, if_pos ⟨hx, he⟩]
  · rw [if_neg he, if_neg fun h => he h.2]

theorem eg_vtx : Spec.eg_vtx := by
  intro v L σj σe σx hL hx hj he hxx W b
  refine (vtx3 v (first ppref L + 5) ppref.d ppref.nexp ppref.fe 2 .low .low .high σj σe σx
      (by decide) (by decide) (by decide) (unit_x hL hx rfl) (by decide) (by decide)
      (by decide) hj he hxx W b).trans
    (congrArg (algebraMap Cb.Gl.F Cb.Gl.E) ?_)
  exact routed_eq hx
    (fun e =>
      FFSeg.matR ppref.d ppref.fe fun j x =>
        FFSeg.entryR ppref kRef W (first ppref L + 5) (uGUr ppref) [j, e, x])
    _ _ _

theorem eu_vtx : Spec.eu_vtx := by
  intro v L σj σe σx hL hx hj he hxx W b
  refine (vtx3 v (first ppref L + 6) ppref.d ppref.nexp ppref.fe 2 .low .low .high σj σe σx
      (by decide) (by decide) (by decide) (unit_x hL hx rfl) (by decide) (by decide)
      (by decide) hj he hxx W b).trans
    (congrArg (algebraMap Cb.Gl.F Cb.Gl.E) ?_)
  exact routed_eq hx
    (fun e =>
      FFSeg.matR ppref.d ppref.fe fun j x =>
        FFSeg.entryR ppref kRef W (first ppref L + 6) (uGUr ppref) [j, e, x])
    _ _ _

theorem ed_vtx : Spec.ed_vtx := by
  intro v L σj σe σx hL hx hj he hxx W b
  refine (vtx3 v (first ppref L + 8) ppref.fe ppref.nexp ppref.d 2 .low .low .high σj σe σx
      (by decide) (by decide) (by decide) (unit_x hL hx rfl) (by decide) (by decide)
      (by decide) hj he hxx W b).trans
    (congrArg (algebraMap Cb.Gl.F Cb.Gl.E) ?_)
  exact routed_eq hx
    (fun e =>
      FFSeg.matR ppref.fe ppref.d fun j x =>
        FFSeg.entryR ppref kRef W (first ppref L + 8) (uDr ppref) [j, e, x])
    _ _ _

/-! ### Coordinates of kind whole -/

theorem qk_ok : Spec.qk_ok := fun v L σx σj hx hj hOK =>
  r_ok v _ _ _ (widthsQK hx hj) (by
    have : [σx.take 6, σx.drop 6, σj].flatten = σx ++ σj := by simp [← List.append_assoc]
    rw [this]
    exact hOK)

theorem tok_ok : Spec.tok_ok := fun v σt σj ht hj hOK =>
  ⟨r_ok v _ _ _ (widthsTok (k := .high) (by decide) ht hj) (by simpa using hOK),
    r_ok v _ _ _ (widthsTok (k := .low) (by decide) ht hj) (by simpa using hOK)⟩

theorem qk_vtx : Spec.qk_vtx := by
  classical
  intro v L σx σj hL hx hj W b hlt
  have h7 : (σx.drop 6).length = 7 := by rw [List.length_drop, hx]
  have hd := num_lt (σx.drop 6) v b
  rw [h7] at hd
  have hsplit : Src.num σx v b = Src.num (σx.take 6) v b * 2 ^ 7 + Src.num (σx.drop 6) v b := by
    conv_lhs => rw [← List.take_append_drop 6 σx]
    rw [num_append, h7]
  have e1 : Src.num (σx.take 6) v b = Src.num σx v b / 128 := by omega
  have e2 : Src.num (σx.drop 6) v b = Src.num σx v b % 128 := by omega
  have hU : (units ppref)[first ppref L]? = some (uQK ppref) := unitL (m := 0) hL rfl
  rw [aQK, r_vtx v _ _ _ hU (widthsQK hx hj) W b]
  have hn : numsAt [σx.take 6, σx.drop 6, σj] v b =
      [Src.num σx v b / 128, Src.num σx v b % 128, Src.num σj v b] := by
    simp [numsAt, e1, e2]
  rw [hn]
  generalize Src.num σx v b = x at hlt
  generalize Src.num σj v b = j
  have hiff : InRows (uQK ppref).coords kRef [x / 128, x % 128, j] ↔ j < 5120 := by
    have a1 : x / 128 < 64 := by omega
    have a2 : x % 128 < 128 := by omega
    simp [InRows, uQK, ppref, a1, a2]
  by_cases hjj : j < 5120
  · rw [if_pos (hiff.2 hjj)]
    refine congrArg (algebraMap Cb.Gl.F Cb.Gl.E) ?_
    by_cases hx5 : x < 5120
    · rw [if_pos hx5]
      exact (if_pos (⟨hjj, hx5⟩ : j < ppref.d ∧ x < ppref.nq * ppref.ch)).symm
    · rw [if_neg hx5]
      have hk : j < ppref.d ∧ x - 5120 < ppref.nkv * ppref.ch :=
        ⟨hjj, by show x - 5120 < 1024; omega⟩
      refine Eq.trans ?_ (if_pos hk).symm
      have b1 : ppref.nq + (x - 5120) / ppref.ch = x / 128 := by
        show 40 + (x - 5120) / 128 = x / 128; omega
      have b2 : (x - 5120) % ppref.ch = x % 128 := by show (x - 5120) % 128 = x % 128; omega
      rw [b1, b2]
      rfl
  · rw [if_neg (fun h => hjj (hiff.1 h))]
    have z1 : ∀ c, (FFSeg.layerR ppref kRef W L).Wq j c = 0 := fun c => if_neg fun h => hjj h.1
    have z2 : ∀ c, (FFSeg.layerR ppref kRef W L).Wk j c = 0 := fun c => if_neg fun h => hjj h.1
    rw [z1, z2, ite_self, map_zero]

theorem emb_vtx : Spec.emb_vtx := by
  classical
  intro v σt σj ht hj W b hlt
  rw [aEmb, r_vtx v _ _ _ (Bridge.unit_emb ppref) (widthsTok (k := .high) (by decide) ht hj) W b]
  have hiff : InRows (uEmb ppref).coords kRef (numsAt [σt, σj] v b) ↔ Src.num σj v b < 5120 := by
    simp [InRows, numsAt, uEmb, hlt, ppref]
  unfold FFSeg.embR FFSeg.matR
  by_cases h : Src.num σj v b < 5120
  · rw [if_pos (hiff.2 h), if_pos (⟨hlt, h⟩ : Src.num σt v b < ppref.V ∧ Src.num σj v b < ppref.d)]
    rfl
  · rw [if_neg (fun hh => h (hiff.1 hh)),
      if_neg (fun hh : Src.num σt v b < ppref.V ∧ Src.num σj v b < ppref.d => h hh.2), map_zero]

theorem h_vtx : Spec.h_vtx := by
  classical
  intro v σv σj ht hj W b hlt
  rw [aH, r_vtx v _ _ _ (Bridge.unit_h ppref) (widthsTok (k := .low) (by decide) ht hj) W b]
  have hiff : InRows (uH ppref).coords kRef (numsAt [σv, σj] v b) ↔ Src.num σj v b < 5120 := by
    simp [InRows, numsAt, uH, hlt, ppref]
  unfold FFSeg.matR
  by_cases h : Src.num σj v b < 5120
  · rw [if_pos (hiff.2 h), if_pos (⟨h, hlt⟩ : Src.num σj v b < ppref.d ∧ Src.num σv v b < ppref.V)]
    rfl
  · rw [if_neg (fun hh => h (hiff.1 hh)),
      if_neg (fun hh : Src.num σj v b < ppref.d ∧ Src.num σv v b < ppref.V => h hh.1), map_zero]

theorem h_int : Spec.h_int := by
  intro M j t
  show (if j < ppref.d ∧ t < ppref.V then _ else 0) =
    (((if j < ppref.d ∧ t < ppref.V then _ else 0 : ℤ) : ℤ) : Cb.Gl.F)
  by_cases h : j < ppref.d ∧ t < ppref.V
  · rw [if_pos h, if_pos h]
    exact entry_cast Cb.Gl.F ppref kRef M _ _ _
  · rw [if_neg h, if_neg h, Int.cast_zero]

end Cm.Seg.TS
