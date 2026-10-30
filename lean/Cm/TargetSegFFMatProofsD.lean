-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFMatProofsD.lean: (V) for the key family QK of the feed-forward segment: queries and
keys with the rotation, over p = 2^64 - 2^32 + 1.

Proofs: `live_QK`. (V): for g < `nGr`, at the vertex of an index (ℓ, x, i) of the family, the
family's value is the key of Inst/Model/FF/Trace.lean (the head of Cm/TargetSegFFAffPass.lean). The
family is `matKeyFam`, a family of lookup keys of the model's arithmetisation
(Cm/TargetSegFFMat.lean, whose head tells families, blocks and vertices); `live_QK` is a case of
`Spec.matKey_live`, which is proved in Cm/TargetSegFFMatProofsE.lean.

Main names:
  `live_QK` (stated here): family QK (queries and keys): the value at the vertex of (ℓ, x, i):
    `FFSeg.key`.

`num_bit` is Cm/SegFFMatProofsD.lean's.
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
import Cm.SegFFMatProofsD
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

/-- what the atom of queries and keys (`aQK`) reads at (j, x'), under the hypotheses of
`Spec.qk_vtx` (Cm/TargetSegIdxModel.lean), among them x' < 6,144 -/
def ωqk (l j x' : ℕ) : Cb.Gl.E :=
  algebraMap Cb.Gl.F Cb.Gl.E
    (if x' < 5120 then (FFSeg.layerR ppref Layout.kRef W (4 * g + l)).Wq j x'
      else (FFSeg.layerR ppref Layout.kRef W (4 * g + l)).Wk j (x' - 5120))

omit scl in
theorem AY_sum (t : FFSeg.Cell → Cb.Gl.E) (l x' i : ℕ) :
    FFSeg.AY DF t (wOf g W) l x' i = ∑ j ∈ range DF.d, FFSeg.val t .a l j i * ωqk g W l j x' := by
  unfold FFSeg.AY FFSeg.Aq FFSeg.Ak ωqk
  rw [show DF.dq = 5120 from rfl]
  split_ifs <;> rfl

theorem live_QK (hg : g < nGr) {l x i : ℕ} (hl : l < DF.nl)
    (hx : x < FFSeg.len DF .QK) (hi : i < DF.T) :
    (matKeyFam (X := X) g tb .QK).val fmtRef x₀ W A (enc3 (vxOf .QK) l x i) =
      FFSeg.key DF (tA g A) tb (4 * g) (wOf g W) .QK l x i := by
  obtain ⟨hd, h⟩ := val_mlive g tb x₀ W A .QK (l := l) rfl hx hi
  have hl4 : l < 4 := hl
  have hg12 : g < 12 := hg
  have hx6 : x < 6144 := hx
  rw [h]
  unfold wpart
  rw [val_mblk_live x₀ W A .QK _ _ _ _ _ hd ⟨hx, rfl⟩]
  simp only [vx_QK] at hd ⊢
  refine (congrArg (fun z => (cLow g .QK l x i : CForm Cb.Gl.E).val A + z)
    (sum_congr rfl fun j hj =>
      (?_ : _ = wsc (FFSeg.kQK DF l x) *
          (rot tb (4 * g + l) x i 0 *
              ((gVal g .a l j i : CForm Cb.Gl.E).val A * ωqk g W l j (x / 2 * 2)) +
            rot tb (4 * g + l) x i 1 *
              ((gVal g .a l j i : CForm Cb.Gl.E).val A * ωqk g W l j (x / 2 * 2 + 1)))))).trans ?_
  · have hj' := mem_range.1 hj
    simp only [ite_mul, zero_mul]
    rw [sum_half hl4, show 2 * l / 2 = l by omega, show (2 * l + 1) / 2 = l by omega,
      show 2 * l % 2 = 0 by omega, show (2 * l + 1) % 2 = 1 by omega]
    have n0 : Src.num (Src.run 2 12 ++ [.bit (0 == 1)])
          (2 + 13 + 10 + 13) (enc3 13 l x i * 2 ^ 13 + j) = x / 2 * 2 := by
      rw [num_bit, num_xhi (n := 12) (m := 1) rfl hd hj']
      simp
    have n1 : Src.num (Src.run 2 12 ++ [.bit (1 == 1)])
          (2 + 13 + 10 + 13) (enc3 13 l x i * 2 ^ 13 + j) =
        x / 2 * 2 + 1 := by
      rw [num_bit, num_xhi (n := 12) (m := 1) rfl hd hj']
      simp
    rw [qk_vtx _ _ _ _ (by omega) (by simp [run_length]) (by rw [run_length]; norm_num)
          W _ (by rw [n0]; omega),
      qk_vtx _ _ _ _ (by omega) (by simp [run_length]) (by rw [run_length]; norm_num)
        W _ (by rw [n1]; omega),
      n0, n1, num_j rfl hj']
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    unfold ωqk
    ring
  · show _ + _ = _
    rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum,
      sum_gVal g A .a l i (N := 2 ^ 13) (by show 5120 ≤ 2 ^ 13; norm_num),
      sum_gVal g A .a l i (N := 2 ^ 13) (by show 5120 ≤ 2 ^ 13; norm_num),
      show FFSeg.Arr.width DF FFSeg.Arr.a = DF.d from rfl, ← AY_sum, ← AY_sum]
    show _ = Site.ssite (FFSeg.Y' DF (tA g A) tb (4 * g) (wOf g W) l x i) _ _ _
    rw [Site.ssite_split, Site.scl_eq]
    have hlow : (cLow g .QK l x i : CForm Cb.Gl.E).val A =
        Site.ssite 0 (FFSeg.val (tA g A) .qkw l x i)
          (FFSeg.val (tA g A) .rqk l x i) (FFSeg.kQK DF l x) := by
      unfold cLow
      rw [val_cSs, val_cVal, val_cVal]
    rw [hlow]
    unfold FFSeg.Y' rot wsc
    have hch : DF.P.ch = 128 := rfl
    by_cases hpar : x % DF.P.ch % 2 = 0
    · have e0 : x / 2 * 2 = x := by rw [hch] at hpar; omega
      simp only [if_pos hpar, e0, if_true, one_ne_zero, if_false]
      ring
    · have e0 : x / 2 * 2 = x - 1 := by rw [hch] at hpar; omega
      have e1 : x - 1 + 1 = x := by rw [hch] at hpar; omega
      simp only [if_neg hpar, e0, e1, if_true, one_ne_zero, if_false]
      ring

end Cm.Seg.TS
