-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFMatProofsC.lean: (V) for the key family D (down projection) of the feed-forward
segment: products of two forms in cells (values of arrays) with a weight; with experts, of three
with a weight, over p = 2^64 - 2^32 + 1.

Proofs: `live_D`; `val_blkDA`, `val_blkDB`: its two blocks, under the hypotheses of their
statements. (V): for g < `nGr`, at the vertex of an index (ℓ, x, i) of the family, the family's
value is the key of Inst/Model/FF/Trace.lean (the head of Cm/TargetSegFFAffPass.lean). The family
is `matKeyFam`, a family of lookup keys of the model's arithmetisation (Cm/TargetSegFFMat.lean,
whose head tells families, blocks and vertices); `live_D` is a case of `Spec.matKey_live`, which is
proved in Cm/TargetSegFFMatProofsE.lean.

Main names:
  `val_blkDA` (stated here): the value of the block of products of two forms in cells with a weight.
  `val_blkDB` (stated here): the value of the block of products of three forms in cells with a
    weight.
  `live_D` (stated here): family D (down projection): the value at the vertex of (ℓ, x, i):
    `FFSeg.key`.

The fields are
`Cb.Gl.F`, `Cb.Gl.E` (Cb/Gl/GlField.lean);
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
natural numbers; hypotheses `hl`, `hx`, `hi` (in `live_D`): below `DF.nl` (layers ℓ of the
segment), `FFSeg.len DF s` (n_s: the length of a family), `DF.T` (positions i) (all three:
Inst/Model/FF/Index.lean); `enc3 (vxOf s) l x i`: a natural number; in `Spec.matKey_live`
(Cm/TargetSegFFMat.lean), the vertex of (ℓ, x, i); `b`: a natural number; in `val_blk`
(Cm/SegFFMatKit.lean), the vertex b = (ℓ | x | i); here by the hypothesis `hd`; `liv s l x`
(Cm/SegFFMat.lean): whether (ℓ, x) is an index of the family; `ia`: ℕ → `IdxAtom Cb.Gl.E`; in `blk`
(Cm/SegFFMatKit.lean), the n index atoms, one monomial for each; `ω`: ℕ → `Cb.Gl.E` (in
`val_blkDB`: ℕ → ℕ → `Cb.Gl.E`); under `hia`, what the atom of layer ℓ reads at (b, j) (`val_blk1`;
with two arguments as in `val_blkR`; Cm/TargetSegFFMatProofs.lean).

The statements and their limits: Cm/TargetSegFFMat.lean, the head,
Limits.

-/
import Cm.SegFFMatProofsB
import Cm.TargetSegAll
import Cm.TargetSegFFMatProofsB
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

/-- in a layer with experts the down projection of the shared expert is 0 from row fe on -/
theorem Wd_zero {l j : ℕ} (x : ℕ) (ho : l % 2 = 1) (hj : DF.fe ≤ j) :
    (wOf (E := Cb.Gl.E) g W l).Wd j x = 0 := by
  have hex : hasExperts (4 * g + l) := by
    show (4 * g + l) % 2 = 1
    omega
  have h0 : (FFSeg.layerR ppref Layout.kRef W (4 * g + l)).Wd j x = 0 := by
    simp only [FFSeg.layerR, if_pos hex, FFSeg.matR]
    exact if_neg fun h => absurd h.1 (Nat.not_lt.2 hj)
  show algebraMap Cb.Gl.F Cb.Gl.E _ = 0
  rw [h0, map_zero]

theorem val_blkDA (ia : ℕ → IdxAtom Cb.Gl.E) (ω : ℕ → Cb.Gl.E) {b l x i : ℕ}
    (hd : dec3 (vxOf .D) b = (l, x, i)) (hL : liv .D l x) (hl : l < 4)
    (hia : ∀ j < 2 ^ 14, (ia l).at fmtRef W (vtx (2 + vxOf .D + 10 + 14) (b * 2 ^ 14 + j)) = ω j) :
    Ex1.val fmtRef x₀ W A
        (mblk .D 14 4 (fun k l _ _ _ => if l = k then wsc (DF.Pl l).kd else 0)
          [fun l _ i j => cVal g .sl l j i, fun l _ i j => cVal g .up l j i] ia)
        (2 + vxOf .D + 10) b =
      wsc (DF.Pl l).kd * ∑ j ∈ range (2 ^ 14), FFSeg.hh (tA g A) l j i * ω j := by
  rw [val_mblk_live x₀ W A .D _ _ _ _ _ hd hL, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  simp only [ite_mul, zero_mul]
  rw [sum_pick hl, hia j (mem_range.1 hj)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, val_cVal]
  rfl

theorem val_blkDB (ia : ℕ → IdxAtom Cb.Gl.E) (ω : ℕ → ℕ → Cb.Gl.E) {b l x i : ℕ}
    (hd : dec3 (vxOf .D) b = (l, x, i)) (hL : liv .D l x) (hl : l < 4) (ho : l % 2 = 1)
    (hia : ∀ e < 2 ^ 7, ∀ j < 2 ^ 13,
      (ia (l / 2)).at fmtRef W (vtx (2 + vxOf .D + 10 + 20) (b * 2 ^ 20 + (e * 2 ^ 13 + j))) =
        ω e j) :
    Ex1.val fmtRef x₀ W A
        (mblk .D 20 2 (fun k l _ _ _ => if l = 2 * k + 1 then wsc (DF.Pl l).kd else 0)
          [fun l _ i j => cVal g .sel (l / 2) (j / 2 ^ 13) i,
            fun l _ i j => cVal g .sl l (DF.fe + j % 2 ^ 13) i,
            fun l _ i j => cVal g .up l (DF.fe + j % 2 ^ 13) i] ia)
        (2 + vxOf .D + 10) b =
      wsc (DF.Pl l).kd *
        ∑ e ∈ range DF.nx, FFSeg.val (tA g A) .sel (l / 2) e i *
          ∑ j ∈ range DF.fe, FFSeg.hh (tA g A) l (DF.fe + j) i * ω e j := by
  have hr : range (2 ^ 20) = range (2 ^ 7 * 2 ^ 13) := by norm_num
  have hnx : DF.nx = 2 ^ 7 := rfl
  have hfe : range DF.fe = range (2 ^ 13) := rfl
  rw [val_mblk_live x₀ W A .D _ _ _ _ _ hd hL, hr, Alg.sum_range_mul_add, mul_sum, hnx, hfe]
  refine sum_congr rfl fun e he => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  simp only [ite_mul, zero_mul]
  rw [sum_odd (n := 2) (by omega), if_pos ho, hia e (mem_range.1 he) j hj']
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [(div_mod_of hj').1, (div_mod_of hj').2, val_cVal, val_cVal, val_cVal]
  unfold FFSeg.hh
  ring

theorem live_D (hg : g < nGr) {l x i : ℕ} (hl : l < DF.nl)
    (hx : x < FFSeg.len DF .D) (hi : i < DF.T) :
    (matKeyFam (X := X) g tb .D).val fmtRef x₀ W A (enc3 (vxOf .D) l x i) =
      FFSeg.key DF (tA g A) tb (4 * g) (wOf g W) .D l x i := by
  obtain ⟨hd, h⟩ := val_mlive g tb x₀ W A .D (l := l) rfl hx hi
  have hl4 : l < 4 := hl
  have hg12 : g < 12 := hg
  rw [h]
  unfold wpart
  rw [val1_add, val_blkDA g x₀ W A _ (fun j => (wOf g W l).Wd j x) hd ⟨hx, rfl⟩ hl4 fun j hj => by
    rw [d_vtx _ _ _ _ (by omega) (by rw [run_length]; exact fOf_le _)
          (by rw [run_length]; norm_num),
      num_j (by rw [vx_D]) hj]
    simp only [vx_D] at hd ⊢
    rw [num_x hd hj]
    rfl]
  show _ = Site.ssite (FFSeg.Ad DF (tA g A) (wOf g W) l x i) _ _ _
  rw [Site.ssite_split, Site.scl_eq]
  have hlow : (cLow g .D l x i : CForm Cb.Gl.E).val A =
      Site.ssite 0 (FFSeg.xS DF (tA g A) (2 * l + 2) x i - FFSeg.xS DF (tA g A) (2 * l + 1) x i)
        (FFSeg.val (tA g A) .rd l x i) (DF.Pl l).kd := by
    unfold cLow
    rw [val_cSs, val_sub, val_mXS, val_mXS, val_cVal]
  rw [hlow]
  unfold FFSeg.Ad
  by_cases ho : l % 2 = 1
  · have hE : FFSeg.isExpL l = true := by simp [FFSeg.isExpL, ho]
    have e2 : 2 * (l / 2) + 1 = l := by omega
    rw [val_blkDB g x₀ W A _ (fun e j => (wOf g W l).Ed e j x) hd ⟨hx, rfl⟩ hl4 ho fun e he j hj => by
      have hjj : e * 2 ^ 13 + j < 2 ^ 20 := by
        have : e * 2 ^ 13 + j < 2 ^ 7 * 2 ^ 13 := by nlinarith
        simpa using this
      rw [e2,
        ed_vtx _ _ _ _ _ (by omega) (by show (4 * g + l) % 2 = 1; omega)
          (by rw [run_length]; norm_num) (by rw [run_length]; norm_num)
          (by rw [run_length]; norm_num),
        num_jhi (n := 7) (m := 13) (by rw [vx_D]) rfl hjj,
        num_jlo (n := 7) (m := 13) (by rw [vx_D]) rfl, (div_mod_of hj).1, (div_mod_of hj).2]
      simp only [vx_D] at hd ⊢
      rw [num_x hd hjj]
      rfl]
    rw [if_pos hE,
      sum_cut (n := DF.fe) (N := 2 ^ 14) (by show 8192 ≤ 2 ^ 14; norm_num) _
        fun j hj _ => by rw [Wd_zero g W x ho hj, mul_zero]]
    unfold wsc
    ring
  · have hE : ¬ FFSeg.isExpL l = true := by simp [FFSeg.isExpL, ho]
    rw [val_mblk_zero x₀ W A .D _ _ _ _ _ hd fun k j => if_neg (by omega),
      if_neg hE, show DF.f = 2 ^ 14 from rfl]
    unfold wsc
    ring

end Cm.Seg.TS
