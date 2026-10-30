-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFMatProofsA.lean: (V) for the key families V, O, LR of the feed-forward segment: one
block, one form in cells (the value of an array) in a monomial, over p = 2^64 - 2^32 + 1.

Proofs: `live_V`, `live_O`, `live_LR`. (V): for g < `nGr`, at the vertex of an index (ℓ, x, i) of
the family, the family's value is the key of Inst/Model/FF/Trace.lean (the head of
Cm/TargetSegFFAffPass.lean). The family is `matKeyFam`, a family of lookup keys of the model's
arithmetisation (Cm/TargetSegFFMat.lean, whose head tells families, blocks and vertices); these are
cases of `Spec.matKey_live`, which is proved in Cm/TargetSegFFMatProofsE.lean.

Main names:
  `live_V` (stated here): family V: the value at the vertex of (ℓ, x, i): `FFSeg.key`.
  `live_O` (stated here): family O: the value at the vertex of (ℓ, x, i): `FFSeg.key`.
  `live_LR` (stated here): family LR (router): the value at the vertex of (ℓ, x, i): `FFSeg.key`.

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
natural numbers; hypotheses `hl`, `hx`, `hi`: below `DF.nl` (layers ℓ of the segment),
`FFSeg.len DF s` (n_s: the length of a family), `DF.T` (positions i) (all three:
Inst/Model/FF/Index.lean); `enc3 (vxOf s) l x i`: a natural number; in `Spec.matKey_live`
(Cm/TargetSegFFMat.lean), the vertex of (ℓ, x, i); `FFSeg.present s l` (Inst/Model/FF/Index.lean):
whether the family is present in layer ℓ (`hp`, in `live_LR`).

The statements and their limits: Cm/TargetSegFFMat.lean, the head,
Limits.




-/
import Cm.SegFFMatProofs
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

theorem live_V (hg : g < nGr) {l x i : ℕ} (hl : l < DF.nl)
    (hx : x < FFSeg.len DF .V) (hi : i < DF.T) :
    (matKeyFam (X := X) g tb .V).val fmtRef x₀ W A (enc3 (vxOf .V) l x i) =
      FFSeg.key DF (tA g A) tb (4 * g) (wOf g W) .V l x i := by
  obtain ⟨hd, h⟩ := val_mlive g tb x₀ W A .V (l := l) rfl hx hi
  have hl4 : l < 4 := hl
  have hg12 : g < 12 := hg
  rw [h]
  unfold wpart
  rw [val_mblk_live x₀ W A .V _ _ _ _ _ hd ⟨hx, rfl⟩]
  simp only [vx_V] at hd ⊢
  have hin : ∀ j ∈ range (2 ^ 13), ∑ k ∈ range 4, (if l = k then wsc (DF.Pl l).kv else 0) *
        (([fun l _ i j => gVal g .a l j i].map fun f : ℕ → ℕ → ℕ → ℕ → CForm Cb.Gl.E =>
            (f l x i j).val A).prod *
          (aV (4 * g + k) (Src.run 22 13) (Src.run 2 10)).at
            fmtRef W (vtx (2 + 10 + 10 + 13) (enc3 10 l x i * 2 ^ 13 + j))) =
      wsc (DF.Pl l).kv * ((gVal g .a l j i : CForm Cb.Gl.E).val A * (wOf g W l).Wv j x) := by
    intro j hj
    have hj' := mem_range.1 hj
    simp only [ite_mul, zero_mul]
    rw [sum_pick hl4,
      v_vtx _ _ _ _ (by omega) (by rw [run_length]; norm_num) (by rw [run_length]; norm_num),
      num_j rfl hj', num_x hd hj']
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl
  rw [sum_congr rfl hin, ← mul_sum,
    sum_gVal g A .a l i (N := 2 ^ 13) (by show 5120 ≤ 2 ^ 13; norm_num)]
  show _ = Site.ssite (FFSeg.Av DF (tA g A) (wOf g W) l x i) _ _ _
  rw [Site.ssite_split, Site.scl_eq, add_comm]
  unfold cLow
  rw [val_cSs, val_cVal, val_cVal]
  rfl

theorem live_O (hg : g < nGr) {l x i : ℕ} (hl : l < DF.nl)
    (hx : x < FFSeg.len DF .O) (hi : i < DF.T) :
    (matKeyFam (X := X) g tb .O).val fmtRef x₀ W A (enc3 (vxOf .O) l x i) =
      FFSeg.key DF (tA g A) tb (4 * g) (wOf g W) .O l x i := by
  obtain ⟨hd, h⟩ := val_mlive g tb x₀ W A .O (l := l) rfl hx hi
  have hl4 : l < 4 := hl
  have hg12 : g < 12 := hg
  rw [h]
  unfold wpart
  rw [val_blk1 g x₀ W A .O 13 .o (by show 5120 ≤ 2 ^ 13; norm_num) (fun l _ => wsc (DF.Pl l).ko) _ (fun j => (wOf g W l).Wo j x) hd ⟨hx, rfl⟩ hl4 fun j hj => by
    rw [o_vtx _ _ _ _ (by omega) (by rw [run_length]; norm_num) (by rw [run_length]; norm_num),
      num_j (by rw [vx_O]) hj]
    simp only [vx_O] at hd ⊢
    rw [num_x hd hj]
    rfl]
  show _ = Site.ssite (∑ j ∈ range DF.dq, FFSeg.val (tA g A) .o l j i * (wOf g W l).Wo j x) _ _ _
  rw [Site.ssite_split, Site.scl_eq, add_comm]
  unfold cLow
  rw [val_cSs, val_sub, val_mXS, val_mXS, val_cVal]
  rfl

theorem live_LR (hg : g < nGr) {l x i : ℕ} (hl : l < DF.nl) (hp : FFSeg.present .LR l = true)
    (hx : x < FFSeg.len DF .LR) (hi : i < DF.T) :
    (matKeyFam (X := X) g tb .LR).val fmtRef x₀ W A (enc3 (vxOf .LR) l x i) =
      FFSeg.key DF (tA g A) tb (4 * g) (wOf g W) .LR l x i := by
  obtain ⟨hd, h⟩ := val_mlive g tb x₀ W A .LR hp hx hi
  have hl4 : l < 4 := hl
  have hg12 : g < 12 := hg
  have ho : l % 2 = 1 := by simpa [FFSeg.present, FFSeg.isExp, FFSeg.isExpL] using hp
  have e2 : 2 * (l / 2) + 1 = l := by omega
  rw [h]
  unfold wpart
  rw [val_mblk_live x₀ W A .LR _ _ _ _ _ hd ⟨hx, hp⟩]
  simp only [vx_LR] at hd ⊢
  refine (congrArg (fun z => (cLow g .LR l x i : CForm Cb.Gl.E).val A + z)
    (sum_congr rfl fun j hj =>
      (?_ : _ = wsc (DF.Pl l).kr *
          ((gVal g .m l j i : CForm Cb.Gl.E).val A * (wOf g W l).Wr j x)))).trans ?_
  · have hj' := mem_range.1 hj
    simp only [ite_mul, zero_mul]
    rw [sum_odd (n := 2) (by omega), if_pos ho, e2,
      r_vtx' _ _ _ _ (by omega) (by show (4 * g + l) % 2 = 1; omega)
        (by rw [run_length]; norm_num) (by rw [run_length]; norm_num),
      num_j rfl hj', num_x hd hj']
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl
  · show _ + _ = _
    rw [← mul_sum, sum_gVal g A .m l i (N := 2 ^ 13) (by show 5120 ≤ 2 ^ 13; norm_num)]
    show _ = Site.ssite (∑ j ∈ range DF.d, FFSeg.val (tA g A) .m l j i * (wOf g W l).Wr j x)
        (FFSeg.lw (tA g A) (l / 2) x i) _ _
    rw [Site.ssite_split, Site.scl_eq, add_comm]
    unfold cLow FFSeg.lw
    rw [val_cSs, val_add, val_smul, val_cVal, val_cVal, val_cVal]
    rfl

end Cm.Seg.TS
