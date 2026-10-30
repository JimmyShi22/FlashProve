-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/OffMax.lean: region M of an attention segment: the sum MS2M in terms of
the cells.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean).
Main names:
  `blkRow_sum`: a sum over the row blocks under the weights `blkRow` (Inst/Model/Att/Points.lean) is
    the sum over the pairs (P, s) with s < 2 hP - 1 (by `Dim.blk_of_slot`,
    Inst/Model/Att/Index.lean).
  `msM_eq`: the maxima's term on M is `rd2` under the weights `psiRow`, for any array a over (g, i)
    (by `Dim.sum_blocks2`).
Limits: no hypothesis on sizes. Coordinate 0 of a point belongs to the most significant bit, as in
Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.OffGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E] (D : AttSeg.Dim) (C : AttSeg.Calls)

theorem blkRow_sum (vP vs : ℕ → E) (h : ℕ → E) :
    ∑ I ∈ range D.nBlk, AttSeg.blkRow D vP vs I * h I =
      ∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), Blocks.eqN D.lP 0 vP P *
          Blocks.eqN (D.lP + 1) 0 vs s * h (D.rowBlk P s) := by
  unfold AttSeg.blkRow
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hlt := (D.blk_of_slot (Finset.mem_range.1 hP) (Finset.mem_range.1 hs)).2.1
  rw [Finset.sum_eq_single (D.rowBlk P s)]
  · rw [if_pos rfl]
  · intro I _ hI
    rw [if_neg (Ne.symm hI), zero_mul]
  · intro hn
    exact absurd (Finset.mem_range.2 hlt) hn

/-- The maxima's term on region M, for any array a over (g, i). -/
theorem msM_eq (a : ℕ → ℕ → E) (u zs zi : ℕ → E) :
    Blocks.ext (D.lg + D.lP) (fun Y => ∑ s ∈ range (2 ^ (D.lP + 1) - 1),
        Blocks.eqN (D.lP + 1) 0 zs s *
        Blocks.ext D.lB (fun i' => a (Y / D.hP) (D.B * D.rowBlk (Y % D.hP) s + i')) zi) u =
      AttSeg.rd2 D (AttSeg.sh u 0) (AttSeg.psiRow D (AttSeg.sh u D.lg) zs zi) a := by
  rw [ext_split', sh_zero, ext_def]
  unfold AttSeg.rd2
  rw [show D.nG = 2 ^ D.lg from rfl]
  refine Finset.sum_congr rfl fun g _ => ?_
  have R' : ∑ i ∈ range D.T, Blocks.eqN D.lg 0 u g * AttSeg.psiRow D (AttSeg.sh u D.lg) zs zi i *
      a g i =
      ∑ i ∈ range (D.B * D.nBlk), Blocks.eqN D.lg 0 u g *
          (Blocks.eqN D.lB 0 zi (i % D.B) * AttSeg.blkRow D (AttSeg.sh u D.lg) zs (i / D.B)) *
        a g (D.B * (i / D.B) + i % D.B) := by
    rw [show D.T = D.B * D.nBlk from Nat.mul_comm _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.div_add_mod]
    rfl
  have R : ∑ i ∈ range D.T, Blocks.eqN D.lg 0 u g * AttSeg.psiRow D (AttSeg.sh u D.lg) zs zi i *
      a g i =
      Blocks.eqN D.lg 0 u g * ∑ I ∈ range D.nBlk, AttSeg.blkRow D (AttSeg.sh u D.lg) zs I *
        Blocks.ext D.lB (fun i' => a g (D.B * I + i')) zi := by
    rw [R', ← D.sum_blocks2 (fun I i' => Blocks.eqN D.lg 0 u g *
        (Blocks.eqN D.lB 0 zi i' * AttSeg.blkRow D (AttSeg.sh u D.lg) zs I) *
        a g (D.B * I + i')) D.nBlk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [ext_def, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  rw [R, blkRow_sum, nBlk_pow, ext_def, show D.hP = 2 ^ D.lP from rfl]
  refine congrArg (Blocks.eqN D.lg 0 u g * ·) (Finset.sum_congr rfl fun P hP => ?_)
  have hP' := Finset.mem_range.1 hP
  rw [div_pow D.lP g hP', mod_pow D.lP g hP', Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

end Inst.Model.AttSeg.KeyFormsExt
