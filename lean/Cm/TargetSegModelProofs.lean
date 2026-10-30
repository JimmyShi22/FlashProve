-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegModelProofs.lean: the statements of Cm/TargetSegModel.lean, proved: putting together.

The content of these proofs lies in other files. The assemblies of the 25 segments:
Cm/TargetSegFFAllProofs.lean, Cm/TargetSegAtt.lean with Cm/TargetSegAttOK.lean,
Cm/TargetSegHeadAsm.lean with Cm/TargetSegHeadY.lean; put together in Cm/TargetSegModelOf.lean
(`segsOK_of`). The equivalence from `SegsOK`: Cm/TargetSegAllProofs.lean. Bounds and the dictionary
between traces and matrices: Cm/SegLayoutProofs.lean, Cm/SegLayoutPlainProofs.lean (no field occurs
there). The language:
Cm/TargetPRelProofs.lean.

Main names (statements and hypotheses: Cm/TargetSegModel.lean):
  `segs_ok`: `SegsOK s (segM s)`, for the model's 25 segments.
  `model_equiv`: the one equivalence at the model: `Cm.TP.Cond Gl.p` ⇔ the conditions of the 25
    `segM s k`.
  `model_admit`: from `Cm.TP.Ryes Gl.p` to small matrices with all segments' conditions.
  `model_force`: from matrices below the relaxed bound with these conditions, and r < e, to
    `Cm.TP.Rno Gl.p`.
  `model_true`: at a lawful table: r < e and such matrices ⇔ a true request (`TrueAt`,
    Cm/RelBase.lean).

Limits: what the head of Cm/TargetSegModel.lean lists as not said is not said here either.
Terms: lean/GLOSSARY.md.
-/
import Cm.TargetSegModel
import Cm.TargetPLangsProofs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All

theorem segs_ok : Spec.segs_ok := fun s => segsOK_of (attOK s)

theorem model_equiv : Spec.model_equiv := fun s W x =>
  ⟨fun M => equiv_of s (segM s) (segs_ok s) W x M, fun T => equiv_to s (segM s) (segs_ok s) W x T⟩

theorem model_admit : Spec.model_admit := by
  intro s i x T h
  obtain ⟨hr, hb, hc⟩ : x.r < x.e ∧ Below2 129 T ∧ TP.Cond Cb.Gl.p s i.mat x T := h
  exact ⟨hr,
    fun q hq =>
      (lay_below Hd.plain plainOK 129 T (by norm_num)).1 ((lay_below_plain 129 T).1 hb) q hq,
    ((model_equiv s i.mat x).2 T).1 hc⟩

theorem model_force : Spec.model_force := by
  intro s i x M hr hb hc
  refine ⟨hr, (lay_below_plain (2 ^ 18) _).2 fun n hn => ?_, ((model_equiv s i.mat x).1 M).2 hc⟩
  show |get (ofMat Hd.plain M) n| < 2 ^ 18
  rw [lay_ofMat_get]
  unfold rd
  rw [if_pos hn]
  exact hb n.place (lay_inShape Hd.plain plainOK n hn)

theorem model_true : Spec.model_true := by
  intro s h i x
  have hp : Cb.Gl.p.Prime := target_p_prime Cb.Gl.F Cb.Gl.p
  refine ⟨⟨?_, fun ht => ?_⟩, fun ht => ?_⟩
  · rintro ⟨hr, M, hb, hc⟩
    exact TP.forces Cb.Gl.p hp targetGl_big s h i x _ (model_force s i x M hr hb hc)
  · obtain ⟨hr, hb, hc⟩ := model_admit s i x _ ((TP.trace_iff Cb.Gl.p hp targetGl_big s h i x).2 ht)
    exact ⟨hr, _, fun q hq => lt_trans (hb q hq) (by norm_num), hc⟩
  · exact (model_admit s i x _ ((TP.trace_iff Cb.Gl.p hp targetGl_big s h i x).2 ht)).2

end Cm.Seg.TS
