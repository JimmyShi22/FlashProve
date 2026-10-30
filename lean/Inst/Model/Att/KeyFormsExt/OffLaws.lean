-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/OffLaws.lean: region M of an attention segment: the sum SS2M in terms of
the cells.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean).
Main names:
  `wb6b`: the public weight of step 6b (`Wb`, Inst/Model/Att/Sums.lean) at a vertex of the cube.
  `ssM_eq`: `sumPhi D C p t .s6b`, the rule value of SS2M, is the sum over b of wp_b times the
    scores' term. The tables of step 6b are 0 at the last s, so the term - ones · ones of the weight
    has no effect.
  `gapM`: the sum over b of wp_b times the extension of the gap on M is the sum for MS2M, minus
    `sumPhi .s6b`, plus C L ones(z_s).
Limits: no hypothesis on sizes; the weights are those of family 1M. Coordinate 0 of a point belongs
to the most significant bit, as in Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.OffMax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E] (D : AttSeg.Dim) (C : AttSeg.Calls) (p : AttSeg.Pub E)
    (t : AttSeg.Raw → E)

/-- the weight of step 6b at a vertex; Z = X / 2^ln = (g | P | s) -/
theorem wb6b (b X : ℕ) :
    AttSeg.Wb D C p .s6b b (Blocks.cubePt (D.lg + D.lP + (D.lP + 1) + D.ln) X) =
      AttSeg.wp D C p.z .m1 b * (Blocks.eqN (D.lg + D.lP) 0 (AttSeg.uM D C p.z)
          (X / 2 ^ D.ln / 2 ^ (D.lP + 1)) *
        (Blocks.eqN (D.lP + 1) 0 (AttSeg.zs D C p.z) (X / 2 ^ D.ln % 2 ^ (D.lP + 1)) -
          AttSeg.ones (D.lP + 1) (AttSeg.zs D C p.z) * if X / 2 ^ D.ln % 2 ^ (D.lP + 1) =
              2 ^ (D.lP + 1) - 1 then 1 else 0)) := by
  show AttSeg.wp D C p.z .m1 b *
      AttSeg.eqPt D.lg (AttSeg.zg D C p.z) (Blocks.cubePt (D.lg + D.lP + (D.lP + 1) + D.ln) X) *
      AttSeg.eqPt D.lP (AttSeg.zP D C p.z)
          (AttSeg.sh (Blocks.cubePt (D.lg + D.lP + (D.lP + 1) + D.ln) X) D.lg) *
      (AttSeg.eqPt (D.lP + 1) (AttSeg.zs D C p.z)
          (AttSeg.sh (Blocks.cubePt (D.lg + D.lP + (D.lP + 1) + D.ln) X) (D.lg + D.lP)) -
        AttSeg.ones (D.lP + 1) (AttSeg.zs D C p.z) *
          AttSeg.ones (D.lP + 1) (AttSeg.sh (Blocks.cubePt (D.lg + D.lP + (D.lP + 1) + D.ln) X)
              (D.lg + D.lP))) = _
  have h0 : AttSeg.eqPt D.lg (AttSeg.zg D C p.z) (Blocks.cubePt (D.lg + D.lP + (D.lP + 1) + D.ln) X)
      =
      Blocks.eqN D.lg 0 (AttSeg.uM D C p.z) (X / 2 ^ D.ln / 2 ^ (D.lP + 1) / 2 ^ D.lP) := by
    have h := eqPt_seg (D.lg + D.lP + (D.lP + 1) + D.ln) 0 D.lg (D.lP + (D.lP + 1) + D.ln) X (by
      omega) (AttSeg.zg D C p.z)
    rw [sh_zero, eqN_mod] at h
    rw [h, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_add, ← pow_add]
    have e : D.ln + (D.lP + 1 + D.lP) = D.lP + (D.lP + 1) + D.ln := by omega
    rw [e]
    show Blocks.eqN D.lg 0 (AttSeg.sh (AttSeg.uM D C p.z) 0) _ = _
    rw [sh_zero]
  have h1 : AttSeg.eqPt D.lP (AttSeg.zP D C p.z)
      (AttSeg.sh (Blocks.cubePt (D.lg + D.lP + (D.lP + 1) + D.ln) X) D.lg) =
      Blocks.eqN D.lP 0 (AttSeg.sh (AttSeg.uM D C p.z) D.lg) (X / 2 ^ D.ln / 2 ^ (D.lP + 1)) := by
    rw [eqPt_seg (D.lg + D.lP + (D.lP + 1) + D.ln) D.lg D.lP ((D.lP + 1) + D.ln) X (by omega),
        eqN_mod,
      Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm D.ln (D.lP + 1)]
    rfl
  rw [h0, h1, eqPt_seg (D.lg + D.lP + (D.lP + 1) + D.ln) (D.lg + D.lP) (D.lP + 1) D.ln X (by omega),
    ones_seg (D.lg + D.lP + (D.lP + 1) + D.ln) (D.lg + D.lP) (D.lP + 1) D.ln X (by omega),
    eqN_two D.lg D.lP (AttSeg.uM D C p.z) (X / 2 ^ D.ln / 2 ^ (D.lP + 1))]
  ring

/-- The sum SS2M in terms of the cells. -/
theorem ssM_eq : AttSeg.sumPhi D C p t .s6b =
    ∑ b ∈ range D.nb, AttSeg.wp D C p.z .m1 b *
        Blocks.ext (D.lg + D.lP) (fun Y => ∑ s ∈ range (2 ^ (D.lP + 1) - 1),
      Blocks.eqN (D.lP + 1) 0 (AttSeg.zs D C p.z) s * scM D C p t b Y s) (AttSeg.uM D C p.z) := by
  rw [sumPhi_cube]
  refine Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ → ℕ → E, F = fun Y s n =>
      AttSeg.wp D C p.z .m1 b * (Blocks.eqN (D.lg + D.lP) 0 (AttSeg.uM D C p.z) Y *
        (Blocks.eqN (D.lP + 1) 0 (AttSeg.zs D C p.z) s -
          AttSeg.ones (D.lP + 1) (AttSeg.zs D C p.z) * if s = 2 ^ (D.lP + 1) - 1 then 1 else 0)) *
      (if s < 2 ^ (D.lP + 1) - 1 then
        AttSeg.conB D (AttSeg.zi' D C p.z)
            (fun i' => AttSeg.qryV t b (Y / D.hP) (D.B * D.rowBlk (Y % D.hP) s + i') n) else 0) *
      (if s < 2 ^ (D.lP + 1) - 1 then
        AttSeg.conB D (AttSeg.zj' D C p.z)
            (fun j' => AttSeg.keyV t (D.lamOf b) (Y / D.hP) (D.B * D.colBlk (Y % D.hP) s + j') n)
            else 0) :=
    ⟨_, rfl⟩
  have hsum : ∀ X, AttSeg.Wb D C p .s6b b (Blocks.cubePt (D.lg + D.lP + (D.lP + 1) + D.ln) X) *
      AttSeg.Acube D C p t .s6b b X *
      AttSeg.Bcube D C p t .s6b b X =
          (fun Z n => F (Z / 2 ^ (D.lP + 1)) (Z % 2 ^ (D.lP + 1)) n) (X / 2 ^ D.ln) (X % 2 ^ D.ln)
          := by
    intro X
    have hA : AttSeg.Acube D C p t .s6b b X = if X / 2 ^ D.ln % D.nBlk < D.nBlk - 1 then
        AttSeg.conB D (AttSeg.zi' D C p.z) (fun i' => AttSeg.qryV t b (X / 2 ^ D.ln / D.nBlk / D.hP)
          (D.B * D.rowBlk (X / 2 ^ D.ln / D.nBlk % D.hP) (X / 2 ^ D.ln % D.nBlk) + i')
              (X % 2 ^ D.ln)) else 0 := rfl
    have hB : AttSeg.Bcube D C p t .s6b b X = if X / 2 ^ D.ln % D.nBlk < D.nBlk - 1 then
        AttSeg.conB D (AttSeg.zj' D C p.z)
            (fun j' => AttSeg.keyV t (D.lamOf b) (X / 2 ^ D.ln / D.nBlk / D.hP)
          (D.B * D.colBlk (X / 2 ^ D.ln / D.nBlk % D.hP) (X / 2 ^ D.ln % D.nBlk) + j')
              (X % 2 ^ D.ln)) else 0 := rfl
    rw [wb6b, hA, hB, nBlk_pow, hF]
  obtain ⟨F1, hF1⟩ : ∃ F1 : ℕ → ℕ → E, F1 = fun Z n =>
      F (Z / 2 ^ (D.lP + 1)) (Z % 2 ^ (D.lP + 1)) n := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : ℕ → ℕ → E, F2 = fun Y s => ∑ n ∈ range (2 ^ D.ln), F Y s n := ⟨_, rfl⟩
  have step1 : ∑ X ∈ range (2 ^ (D.lg + D.lP + (D.lP + 1) + D.ln)),
      F1 (X / 2 ^ D.ln) (X % 2 ^ D.ln) =
      ∑ Z ∈ range (2 ^ (D.lg + D.lP + (D.lP + 1))), F2 (Z / 2 ^ (D.lP + 1)) (Z % 2 ^ (D.lP + 1)) :=
          by
    rw [sum_tail (D.lg + D.lP + (D.lP + 1)) D.ln F1, hF1, hF2]
  refine (Finset.sum_congr rfl fun X _ => hsum X).trans ?_
  have e0 : ∑ X ∈ range (2 ^ AttSeg.Step.g D .s6b),
      (fun Z n => F (Z / 2 ^ (D.lP + 1)) (Z % 2 ^ (D.lP + 1)) n) (X / 2 ^ D.ln) (X % 2 ^ D.ln) =
      ∑ X ∈ range (2 ^ (D.lg + D.lP + (D.lP + 1) + D.ln)), F1 (X / 2 ^ D.ln) (X % 2 ^ D.ln) := by
    rw [hF1]
    rfl
  rw [e0, step1, sum_tail (D.lg + D.lP) (D.lP + 1) F2, ext_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have hsplit : 2 ^ (D.lP + 1) = (2 ^ (D.lP + 1) - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.two_pow_pos _)).symm
  conv_lhs => rw [hsplit, Finset.sum_range_succ]
  have hlast : F2 Y (2 ^ (D.lP + 1) - 1) = 0 := by
    rw [hF2, hF]
    refine Finset.sum_eq_zero fun n _ => ?_
    beta_reduce
    rw [if_neg (lt_irrefl _), mul_zero, zero_mul]
  rw [hlast, add_zero, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  rw [hF2, hF]
  unfold scM
  rw [show D.ch = 2 ^ D.ln from rfl, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  beta_reduce
  rw [if_neg (by omega), if_pos hs', if_pos hs']
  ring

/-- The weighted sum of the gap's extensions on region M. -/
theorem gapM [scl : Scl] :
    ∑ b ∈ range D.nb, AttSeg.wp D C p.z .m1 b *
        Blocks.ext D.lM (AttSeg.gp D t .M b) (AttSeg.uM D C p.z) =
      ∑ b ∈ range D.nb, AttSeg.wp D C p.z .m1 b *
          AttSeg.rd2 D (AttSeg.zg D C p.z)
              (AttSeg.psiRow D (AttSeg.zP D C p.z) (AttSeg.zs D C p.z) (AttSeg.zi' D C p.z))
              (AttSeg.mxV t b) -
        AttSeg.sumPhi D C p t .s6b +
        ((D.cutC : ℤ) : E) * AttSeg.LL D C p.z .m1 * AttSeg.ones (D.lP + 1) (AttSeg.zs D C p.z) :=
            by
  rw [ssM_eq]
  unfold AttSeg.LL
  simp only [gpM_ext D C p t, msM_eq D]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show _ * (_ + AttSeg.rd2 D (AttSeg.zg D C p.z)
      (AttSeg.psiRow D (AttSeg.zP D C p.z) (AttSeg.zs D C p.z) (AttSeg.zi' D C p.z))
      (AttSeg.mxV t b) - _) = _
  ring

end Inst.Model.AttSeg.KeyFormsExt
