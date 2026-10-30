-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFMatProofs.lean: what the proofs for the seven key families of the feed-forward
segment that hold a matrix product with weights (`isMat`, Cm/SegFFMat.lean; `matKeyFam`,
Cm/TargetSegFFMat.lean) share, and the proof of `Spec.matKey_dead`, over p = 2^64 - 2^32 + 1. (Key
families of the model's arithmetisation: what a family, a block and a vertex are is told in the
head of Cm/TargetSegFFMat.lean.)

Main names:
  `matKey_dead`: (D): at a dead vertex the value is the padding value of the table.

The numbers
of bits (vx_..), the number that a run of variables forms at a vertex (num_..) and the values of
forms (`val_cSs`, `val_mXS`, `sum_gVal`) are Cm/SegFFMatProofs.lean's. The fields are
`Cb.Gl.F`, `Cb.Gl.E` (Cb/Gl/GlField.lean);
the format is `Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean).


The statements and their limits:
Cm/TargetSegFFMat.lean, the head, Limits.



-/
import Cm.SegFFMatProofs
import Cm.TargetSegAll
import Cm.TargetSegFFMat
import Cm.TargetSegIdxModelProofs
import Cm.TargetSegIdxModel
import Cm.TargetSegFF
import Cm.TargetSegFFAffPass


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All Finset
open Ex

variable [scl : Scl]

/-! ## The family at a vertex -/

section Fam
variable {X : Type} (g : ℕ) (tb : Tables) (x₀ : X) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E)

theorem val_split (s : FFSeg.Fam) (b : ℕ) :
    (matKeyFam (X := X) g tb s).val fmtRef x₀ W A b =
      (lowForm g tb s b : CForm Cb.Gl.E).val A +
        Ex1.val fmtRef x₀ W A (wpart g tb s) (2 + vxOf s + 10) b := by
  unfold matKeyFam matKeyE
  rw [fam_val, val1_add, val1_aff]

/-- a block at a dead vertex -/
theorem val_mblk_dead (s : FFSeg.Fam) (w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → Cb.Gl.E)
    (fs : List (ℕ → ℕ → ℕ → ℕ → CForm Cb.Gl.E)) (ia : ℕ → IdxAtom Cb.Gl.E)
    {b : ℕ} (hb : ¬ Live s b) :
    Ex1.val fmtRef x₀ W A (mblk s w n c fs ia) (2 + vxOf s + 10) b = 0 := by
  unfold mblk
  rw [val_blk]
  have hb' : ¬ liv s (dec3 (vxOf s) b).1 (dec3 (vxOf s) b).2.1 := hb
  exact sum_eq_zero fun j _ => sum_eq_zero fun k _ => by rw [if_neg hb', zero_mul]

/-- a block at a live vertex -/
theorem val_mblk_live (s : FFSeg.Fam) (w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → Cb.Gl.E)
    (fs : List (ℕ → ℕ → ℕ → ℕ → CForm Cb.Gl.E)) (ia : ℕ → IdxAtom Cb.Gl.E) {b l x i : ℕ}
    (hd : dec3 (vxOf s) b = (l, x, i)) (hL : liv s l x) :
    Ex1.val fmtRef x₀ W A (mblk s w n c fs ia) (2 + vxOf s + 10) b =
      ∑ j ∈ range (2 ^ w), ∑ k ∈ range n, c k l x i j *
        ((fs.map fun f => (f l x i j).val A).prod *
          (ia k).at fmtRef W (vtx (2 + vxOf s + 10 + w) (b * 2 ^ w + j))) := by
  unfold mblk
  rw [val_blk, hd]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by rw [if_pos hL]

/-- a block all of whose coefficients vanish at (ℓ, x, i) -/
theorem val_mblk_zero (s : FFSeg.Fam) (w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → Cb.Gl.E)
    (fs : List (ℕ → ℕ → ℕ → ℕ → CForm Cb.Gl.E)) (ia : ℕ → IdxAtom Cb.Gl.E) {b l x i : ℕ}
    (hd : dec3 (vxOf s) b = (l, x, i)) (h0 : ∀ k j, c k l x i j = 0) :
    Ex1.val fmtRef x₀ W A (mblk s w n c fs ia) (2 + vxOf s + 10) b = 0 := by
  unfold mblk
  rw [val_blk, hd]
  exact sum_eq_zero fun j _ => sum_eq_zero fun k _ => by rw [h0 k j, ite_self, zero_mul]

/-- A block with one form in cells (the value of an array) in a monomial, over the four layers, at
a live vertex of a layer ℓ < 4, for an array no wider than 2^w: c(ℓ, x) · ∑_j cell_j · ω_j, where
cell_j is the array's value at j (`FFSeg.val`) and ω_j is what the atom of layer ℓ reads at
(b, j). -/
theorem val_blk1 (s : FFSeg.Fam) (w : ℕ) (Y : FFSeg.Arr) (hw : Y.width DF ≤ 2 ^ w)
    (cc : ℕ → ℕ → Cb.Gl.E) (ia : ℕ → IdxAtom Cb.Gl.E) (ω : ℕ → Cb.Gl.E) {b l x i : ℕ}
    (hd : dec3 (vxOf s) b = (l, x, i)) (hL : liv s l x) (hl : l < 4)
    (hia : ∀ j < 2 ^ w, (ia l).at fmtRef W (vtx (2 + vxOf s + 10 + w) (b * 2 ^ w + j)) = ω j) :
    Ex1.val fmtRef x₀ W A
        (mblk s w 4 (fun k l x _ _ => if l = k then cc l x else 0)
          [fun l _ i j => gVal g Y l j i] ia)
        (2 + vxOf s + 10) b =
      cc l x * ∑ j ∈ range (Y.width DF), FFSeg.val (tA g A) Y l j i * ω j := by
  rw [val_mblk_live x₀ W A s _ _ _ _ _ hd hL, ← sum_gVal g A Y l i hw, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  simp only [ite_mul, zero_mul]
  rw [sum_pick hl, hia j (mem_range.1 hj)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- The block of a routed expert, at a live vertex of a layer ℓ < 4 with experts: c(ℓ, x) · ∑_e
sel_e ∑_j xr_j · ω_(e,j), where ω_(e,j) is what the atom of layer ℓ reads at (b, e · 2^13 + j). -/
theorem val_blkR (s : FFSeg.Fam) (cc : ℕ → ℕ → Cb.Gl.E) (ia : ℕ → IdxAtom Cb.Gl.E)
    (ω : ℕ → ℕ → Cb.Gl.E) {b l x i : ℕ} (hd : dec3 (vxOf s) b = (l, x, i)) (hL : liv s l x)
    (hl : l < 4) (ho : l % 2 = 1)
    (hia : ∀ e < 2 ^ 7, ∀ j < 2 ^ 13,
      (ia (l / 2)).at fmtRef W (vtx (2 + vxOf s + 10 + 20) (b * 2 ^ 20 + (e * 2 ^ 13 + j))) =
        ω e j) :
    Ex1.val fmtRef x₀ W A
        (mblk s 20 2 (fun k l x _ _ => if l = 2 * k + 1 then cc l x else 0)
          [fun l _ i j => cVal g .sel (l / 2) (j / 2 ^ 13) i,
            fun l _ i j => gVal g .xr (l / 2) (j % 2 ^ 13) i] ia)
        (2 + vxOf s + 10) b =
      cc l x * ∑ e ∈ range DF.nx, FFSeg.val (tA g A) .sel (l / 2) e i *
          ∑ j ∈ range DF.d, FFSeg.val (tA g A) .xr (l / 2) j i * ω e j := by
  have hr : range (2 ^ 20) = range (2 ^ 7 * 2 ^ 13) := by norm_num
  have hnx : DF.nx = 2 ^ 7 := rfl
  rw [val_mblk_live x₀ W A s _ _ _ _ _ hd hL, hr, Alg.sum_range_mul_add, mul_sum, hnx]
  refine sum_congr rfl fun e he => ?_
  have h13 : (FFSeg.Arr.xr).width DF ≤ 2 ^ 13 := by
    show 5120 ≤ 2 ^ 13
    norm_num
  have hs := sum_gVal g A .xr (l / 2) i h13 (ω e)
  rw [show DF.d = (FFSeg.Arr.xr).width DF from rfl, ← hs, mul_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  simp only [ite_mul, zero_mul]
  rw [sum_odd (n := 2) (by omega), if_pos ho, hia e (mem_range.1 he) j hj']
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [(div_mod_of hj').1, (div_mod_of hj').2, val_cVal]
  ring

/-- the family at the vertex of an index -/
theorem val_mlive (s : FFSeg.Fam) {l x i : ℕ} (hp : FFSeg.present s l = true)
    (hx : x < FFSeg.len DF s) (hi : i < DF.T) :
    dec3 (vxOf s) (enc3 (vxOf s) l x i) = (l, x, i) ∧
    (matKeyFam (X := X) g tb s).val fmtRef x₀ W A (enc3 (vxOf s) l x i) =
      (cLow g s l x i : CForm Cb.Gl.E).val A +
        Ex1.val fmtRef x₀ W A (wpart g tb s) (2 + vxOf s + 10) (enc3 (vxOf s) l x i) := by
  have hd : dec3 (vxOf s) (enc3 (vxOf s) l x i) = (l, x, i) :=
    dec3_enc3 (lt_of_lt_of_le hx (len_le s)) hi
  have hL : Live s (enc3 (vxOf s) l x i) := by
    unfold Live
    rw [hd]
    exact ⟨hx, hp⟩
  refine ⟨hd, ?_⟩
  rw [val_split]
  unfold lowForm
  rw [if_pos hL, hd]

omit scl in
theorem matKey_dead : Spec.matKey_dead := by
  intro _ X g tb s x₀ W A b hb
  rw [val_split]
  unfold lowForm
  rw [if_neg hb, val_cK]
  have h0 : Ex1.val fmtRef x₀ W A (wpart g tb s) (2 + vxOf s + 10) b = 0 := by
    cases s
    case V | O | LR | QK => exact val_mblk_dead x₀ W A _ _ _ _ _ _ hb
    case G | U | D =>
      unfold wpart
      rw [val1_add, val_mblk_dead x₀ W A _ _ _ _ _ _ hb,
        val_mblk_dead x₀ W A _ _ _ _ _ _ hb, add_zero]
    all_goals exact val1_zero fmtRef x₀ W A _ _
  rw [h0, add_zero]

end Fam
end Cm.Seg.TS
