-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFMatProofsB.lean: (V) for the key families G and U of the feed-forward segment: a
block for dense layers and the shared expert, a block for the routed expert, over
p = 2^64 - 2^32 + 1.

Proofs: `live_G`, `live_U`. (V): for g < `nGr`, at the vertex of an index (ℓ, x, i) of the family,
the family's value is the key of Inst/Model/FF/Trace.lean (the head of Cm/TargetSegFFAffPass.lean).
The family is `matKeyFam`, a family of lookup keys of the model's arithmetisation
(Cm/TargetSegFFMat.lean, whose head tells families, blocks and vertices); these are cases of
`Spec.matKey_live`, which is proved in Cm/TargetSegFFMatProofsE.lean.

Main names:
  `live_G` (stated here): family G (gate projection): the value at the vertex of (ℓ, x, i):
    `FFSeg.key`.
  `live_U` (stated here): family U (up projection): the value at the vertex of (ℓ, x, i):
    `FFSeg.key`.

`fOf_le`, `routed_iff` are Cm/SegFFMatProofsB.lean's.
The fields are `Cb.Gl.F`, `Cb.Gl.E` (Cb/Gl/GlField.lean);
the format is `Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean).


Notation: `g`: a natural number; in `tA g A`, `wOf g W` (Cm/SegPilotKit.lean), group g; `nGr`
(Inst/Model/All/Trace.lean): a natural number: groups of four layers; `tb`: `Tables`
(Inst/Model/Program.lean), the five table functions that the program reads; `W`: ℕ → ℕ → `Cb.Gl.F`;
in `wOf g W`, the index matrix W over F; `A`: ℕ → ℕ → ℕ → `Cb.Gl.E`; in `tA g A`, the matrices;
`tA g A`: `FFSeg.Cell` → `Cb.Gl.E`: the matrices, read as a trace of the feed-forward segment of
group g; `wOf g W`: ℕ → `FFSeg.LW Cb.Gl.E`: the weights that the families of group g read; `DF`
(Inst/Model/All/NoWrap.lean): `FFSeg.Dim` (Inst/Model/FF/Index.lean), the sizes of a feed-forward
segment; := `FFSeg.Dim.ref`; `vxOf s` (Cm/SegPilotAff.lean; s: a family of keys, `FFSeg.Fam`:
Inst/Model/FF/Index.lean): the number of bits of the index x of a family; `l` (ℓ), `x`, `i`:
natural numbers; hypotheses `hl`, `hx`, `hi`: below `DF.nl` (layers ℓ of the segment),
`FFSeg.len DF s` (n_s: the length of a family), `DF.T` (positions i) (all three:
Inst/Model/FF/Index.lean); `enc3 (vxOf s) l x i`: a natural number; in `Spec.matKey_live`
(Cm/TargetSegFFMat.lean), the vertex of (ℓ, x, i).

The statements and their limits: Cm/TargetSegFFMat.lean, the head,
Limits.




-/
import Cm.SegFFMatProofsB
import Cm.TargetSegAll
import Cm.TargetSegFFMatProofs
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

variable [scl : Scl] {X : Type} (g : ℕ) (tb : Tables) (x₀ : X)
  (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E)

theorem live_G (hg : g < nGr) {l x i : ℕ} (hl : l < DF.nl)
    (hx : x < FFSeg.len DF .G) (hi : i < DF.T) :
    (matKeyFam (X := X) g tb .G).val fmtRef x₀ W A (enc3 (vxOf .G) l x i) =
      FFSeg.key DF (tA g A) tb (4 * g) (wOf g W) .G l x i := by
  obtain ⟨hd, h⟩ := val_mlive g tb x₀ W A .G (l := l) rfl hx hi
  have hl4 : l < 4 := hl
  have hg12 : g < 12 := hg
  have hx14 : x < 16384 := hx
  rw [h]
  unfold wpart
  rw [val1_add, val_blk1 g x₀ W A .G 13 .m (by show 5120 ≤ 2 ^ 13; norm_num) (fun l x => if FFSeg.routed DF l x then 0 else wsc (FFSeg.kG DF l x)) _ (fun j => (wOf g W l).Wg j x) hd ⟨hx, rfl⟩ hl4 fun j hj => by
    rw [g_vtx _ _ _ _ (by omega) (by rw [run_length]; norm_num)
          (by rw [run_length]; exact fOf_le _),
      num_j (by rw [vx_G]) hj]
    simp only [vx_G] at hd ⊢
    rw [num_x hd hj]
    rfl]
  show _ = Site.ssite (FFSeg.Ag DF (tA g A) (wOf g W) l x i) _ _ _
  rw [Site.ssite_split, Site.scl_eq]
  have hlow : (cLow g .G l x i : CForm Cb.Gl.E).val A =
      Site.ssite 0 (FFSeg.gw (tA g A) l x i) (FFSeg.val (tA g A) .rg l x i) (FFSeg.kG DF l x) := by
    unfold cLow
    rw [val_cSs, val_add, val_smul, val_cVal, val_cVal, val_cVal]
    rfl
  rw [hlow]
  unfold FFSeg.Ag
  by_cases hr : FFSeg.routed DF l x = true
  · obtain ⟨ho, hfe⟩ := routed_iff.1 hr
    have e2 : 2 * (l / 2) + 1 = l := by omega
    rw [val_blkR g x₀ W A .G (fun l x => if FFSeg.routed DF l x then wsc (FFSeg.kG DF l x) else 0) _ (fun e j => (wOf g W l).Eg e j (x - DF.fe)) hd ⟨hx, rfl⟩ hl4 ho fun e he j hj => by
      have hjj : e * 2 ^ 13 + j < 2 ^ 20 := by
        have : e * 2 ^ 13 + j < 2 ^ 7 * 2 ^ 13 := by nlinarith
        simpa using this
      rw [e2,
        eg_vtx _ _ _ _ _ (by omega) (by show (4 * g + l) % 2 = 1; omega)
          (by rw [run_length]; norm_num) (by rw [run_length]; norm_num)
          (by rw [run_length]; norm_num),
        num_jhi (n := 7) (m := 13) (by rw [vx_G]) rfl hjj,
        num_jlo (n := 7) (m := 13) (by rw [vx_G]) rfl,
        num_xlo (n := 13) (by norm_num) (by rw [vx_G]) hd hjj,
        (div_mod_of hj).1, (div_mod_of hj).2,
        show x % 2 ^ 13 = x - DF.fe from by
          have : DF.fe = 8192 := rfl
          omega]
      rfl]
    simp only [hr, if_true]
    unfold wsc
    ring
  · rw [val_mblk_zero x₀ W A .G _ _ _ _ _ hd fun k j => by simp [hr]]
    simp only [hr]
    unfold wsc
    simp only [Bool.false_eq_true, if_false, add_zero]
    rw [show FFSeg.Arr.width DF FFSeg.Arr.m = DF.d from rfl]
    ring

theorem live_U (hg : g < nGr) {l x i : ℕ} (hl : l < DF.nl)
    (hx : x < FFSeg.len DF .U) (hi : i < DF.T) :
    (matKeyFam (X := X) g tb .U).val fmtRef x₀ W A (enc3 (vxOf .U) l x i) =
      FFSeg.key DF (tA g A) tb (4 * g) (wOf g W) .U l x i := by
  obtain ⟨hd, h⟩ := val_mlive g tb x₀ W A .U (l := l) rfl hx hi
  have hl4 : l < 4 := hl
  have hg12 : g < 12 := hg
  have hx14 : x < 16384 := hx
  rw [h]
  unfold wpart
  rw [val1_add, val_blk1 g x₀ W A .U 13 .m (by show 5120 ≤ 2 ^ 13; norm_num) (fun l x => if FFSeg.routed DF l x then 0 else wsc (FFSeg.kU DF l x)) _ (fun j => (wOf g W l).Wu j x) hd ⟨hx, rfl⟩ hl4 fun j hj => by
    rw [u_vtx _ _ _ _ (by omega) (by rw [run_length]; norm_num)
          (by rw [run_length]; exact fOf_le _),
      num_j (by rw [vx_U]) hj]
    simp only [vx_U] at hd ⊢
    rw [num_x hd hj]
    rfl]
  show _ = Site.ssite (FFSeg.Au DF (tA g A) (wOf g W) l x i) _ _ _
  rw [Site.ssite_split, Site.scl_eq]
  have hlow : (cLow g .U l x i : CForm Cb.Gl.E).val A =
      Site.ssite 0 (FFSeg.val (tA g A) .up l x i)
        (FFSeg.val (tA g A) .ru l x i) (FFSeg.kU DF l x) := by
    unfold cLow
    rw [val_cSs, val_cVal, val_cVal]
  rw [hlow]
  unfold FFSeg.Au
  by_cases hr : FFSeg.routed DF l x = true
  · obtain ⟨ho, hfe⟩ := routed_iff.1 hr
    have e2 : 2 * (l / 2) + 1 = l := by omega
    rw [val_blkR g x₀ W A .U (fun l x => if FFSeg.routed DF l x then wsc (FFSeg.kU DF l x) else 0) _ (fun e j => (wOf g W l).Eu e j (x - DF.fe)) hd ⟨hx, rfl⟩ hl4 ho fun e he j hj => by
      have hjj : e * 2 ^ 13 + j < 2 ^ 20 := by
        have : e * 2 ^ 13 + j < 2 ^ 7 * 2 ^ 13 := by nlinarith
        simpa using this
      rw [e2,
        eu_vtx _ _ _ _ _ (by omega) (by show (4 * g + l) % 2 = 1; omega)
          (by rw [run_length]; norm_num) (by rw [run_length]; norm_num)
          (by rw [run_length]; norm_num),
        num_jhi (n := 7) (m := 13) (by rw [vx_U]) rfl hjj,
        num_jlo (n := 7) (m := 13) (by rw [vx_U]) rfl,
        num_xlo (n := 13) (by norm_num) (by rw [vx_U]) hd hjj,
        (div_mod_of hj).1, (div_mod_of hj).2,
        show x % 2 ^ 13 = x - DF.fe from by
          have : DF.fe = 8192 := rfl
          omega]
      rfl]
    simp only [hr, if_true]
    unfold wsc
    ring
  · rw [val_mblk_zero x₀ W A .U _ _ _ _ _ hd fun k j => by simp [hr]]
    simp only [hr]
    unfold wsc
    simp only [Bool.false_eq_true, if_false, add_zero]
    rw [show FFSeg.Arr.width DF FFSeg.Arr.m = DF.d from rfl]
    ring

end Cm.Seg.TS
