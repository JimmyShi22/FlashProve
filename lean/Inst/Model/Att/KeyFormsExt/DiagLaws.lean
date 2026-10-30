-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/DiagLaws.lean: region D of an attention segment: the sums MS2D and SS2D
in terms of the cells.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean).
Main names:
  `eqN_mod`, `eqN_two`: an equality weight reads the low n bits of its index alone; an equality
    weight over n1 + n2 bits is a product of two.
  `rd2_ext`: `rd2` (Inst/Model/Att/Sums.lean) as nested extensions. `msD_eq`: the extension over (g
    | I) of the sum over i' of eq(z_i', i') a[g, B I + i'] is `rd2` at the point (z̄_I | z_i'), for
    any array a.
  `ssD_eq`: `sumPhi D C p t .s6d`, the rule value of SS2D, is the sum over b of wp_b times the
    extension over (g | I) of the scores' term at u^D.
  `gapD`: the sum over b of wp_b times the extension of the gap on D is the sum for MS2D, minus
    `sumPhi .s6d`, plus Om L (1 - LE(z_j', z_i')).
Limits: `gapD` stands under D.lM ≤ C.Dk ≤ C.a 0; its weights are those of family 1D. Coordinate 0 of
a point belongs to the most significant bit, as in Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.DiagGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E]

/-- an equality weight reads the low n bits of its index alone -/
theorem eqN_mod (n off : ℕ) (u : ℕ → E) (Z : ℕ) : Blocks.eqN n off u (Z % 2 ^ n) =
    Blocks.eqN n off u Z := by
  unfold Blocks.eqN
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [Nat.testBit_mod_two_pow]
  simp [show n - 1 - k < n by omega]

theorem eqN_two (n1 n2 : ℕ) (u : ℕ → E) (Y : ℕ) :
    Blocks.eqN (n1 + n2) 0 u Y = Blocks.eqN n1 0 u (Y / 2 ^ n2) *
        Blocks.eqN n2 0 (AttSeg.sh u n1) Y := by
  conv_lhs => rw [← Nat.div_add_mod' Y (2 ^ n2)]
  rw [Blocks.eqN_append' n1 n2 0 u _ (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.zero_add, eqN_sh n2 n1,
      eqN_mod]

variable (D : AttSeg.Dim) (C : AttSeg.Calls)

/-- rd2 as nested extensions -/
theorem rd2_ext (vg w : ℕ → E) (a : ℕ → ℕ → E) :
    AttSeg.rd2 D vg (AttSeg.eqT D w) a = Blocks.ext D.lg (fun g => Blocks.ext D.lT (a g) w) vg := by
  unfold AttSeg.rd2 AttSeg.eqT
  rw [ext_def, show D.nG = 2 ^ D.lg from rfl, D.T_eq]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [ext_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The maxima's term on region D, for any array a over (g, i). -/
theorem msD_eq (a : ℕ → ℕ → E) (u zi : ℕ → E) :
    Blocks.ext (D.lg + (D.lP + 1))
        (fun Y => Blocks.ext D.lB (fun i' => a (Y / D.nBlk) (D.B * (Y % D.nBlk) + i')) zi) u =
      AttSeg.rd2 D (AttSeg.sh u 0) (AttSeg.eqT D (AttSeg.cat (D.lP + 1) (AttSeg.sh u D.lg) zi)) a :=
          by
  rw [rd2_ext, sh_zero, ext_split', nBlk_pow]
  refine Blocks.ext_congr (fun g _ => ?_) u
  have hT : D.lT = (D.lP + 1) + D.lB := rfl
  rw [hT, ext_split' (D.lP + 1) D.lB]
  have p1 : ∀ k < D.lP + 1, AttSeg.sh u D.lg k = AttSeg.cat (D.lP + 1) (AttSeg.sh u D.lg) zi k := by
    intro k hk
    unfold AttSeg.cat
    rw [if_pos hk]
  rw [Blocks.ext_congr_point p1]
  refine Blocks.ext_congr (fun I hI => ?_) _
  have p2 : ∀ k < D.lB, zi k = AttSeg.sh (AttSeg.cat (D.lP + 1) (AttSeg.sh u D.lg) zi) (D.lP + 1) k
      := by
    intro k _
    unfold AttSeg.sh AttSeg.cat
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
  rw [Blocks.ext_congr_point p2, div_pow _ g hI, mod_pow _ g hI]
  refine Blocks.ext_congr (fun i' _ => ?_) _
  rw [show D.B = 2 ^ D.lB from rfl, Nat.mul_comm]

variable (p : AttSeg.Pub E) (t : AttSeg.Raw → E)

/-- The sum SS2D in terms of the cells. -/
theorem ssD_eq : AttSeg.sumPhi D C p t .s6d =
    ∑ b ∈ range D.nb, AttSeg.wp D C p.z .d1 b *
        Blocks.ext (D.lg + (D.lP + 1)) (scD D C p t b) (AttSeg.uD D C p.z) := by
  rw [sumPhi_cube]
  refine Finset.sum_congr rfl fun b _ => ?_
  show ∑ X ∈ range (2 ^ (D.lg + (D.lP + 1) + D.ln)), _ = _
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ → E, F = fun Y n => AttSeg.wp D C p.z .d1 b *
      (Blocks.eqN (D.lg + (D.lP + 1)) 0 (AttSeg.uD D C p.z) Y *
        (AttSeg.conB D (AttSeg.zi' D C p.z)
            (fun i' => AttSeg.qryV t b (Y / D.nBlk) (D.B * (Y % D.nBlk) + i') n) *
         AttSeg.conB D (AttSeg.zj' D C p.z)
             (fun j' => AttSeg.keyV t (D.lamOf b) (Y / D.nBlk) (D.B * (Y % D.nBlk) + j') n))) :=
             ⟨_, rfl⟩
  have hsum : ∀ X, AttSeg.Wb D C p .s6d b (Blocks.cubePt (D.lg + (D.lP + 1) + D.ln) X) *
      AttSeg.Acube D C p t .s6d b X *
        AttSeg.Bcube D C p t .s6d b X = F (X / 2 ^ D.ln) (X % 2 ^ D.ln) := by
    intro X
    rw [hF]
    have hW : AttSeg.Wb D C p .s6d b (Blocks.cubePt (D.lg + (D.lP + 1) + D.ln) X) =
        AttSeg.wp D C p.z .d1 b * Blocks.eqN (D.lg + (D.lP + 1)) 0 (AttSeg.uD D C p.z)
            (X / 2 ^ D.ln) := by
      show AttSeg.wp D C p.z .d1 b *
          AttSeg.eqPt D.lg (AttSeg.zgD D C p.z) (Blocks.cubePt (D.lg + (D.lP + 1) + D.ln) X) *
        AttSeg.eqPt (D.lP + 1) (AttSeg.zID D C p.z)
            (AttSeg.sh (Blocks.cubePt (D.lg + (D.lP + 1) + D.ln) X) D.lg) = _
      have h0 : AttSeg.eqPt D.lg (AttSeg.zgD D C p.z) (Blocks.cubePt (D.lg + (D.lP + 1) + D.ln) X) =
          Blocks.eqN D.lg 0 (AttSeg.uD D C p.z) (X / 2 ^ D.ln / 2 ^ (D.lP + 1)) := by
        have h := eqPt_seg (D.lg + (D.lP + 1) + D.ln) 0 D.lg ((D.lP + 1) + D.ln) X (by omega)
            (AttSeg.zgD D C p.z)
        rw [sh_zero, eqN_mod] at h
        rw [h, Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm D.ln (D.lP + 1)]
        show Blocks.eqN D.lg 0 (AttSeg.sh (AttSeg.uD D C p.z) 0) _ = _
        rw [sh_zero]
      rw [h0, eqPt_seg (D.lg + (D.lP + 1) + D.ln) D.lg (D.lP + 1) D.ln X (by omega), eqN_mod,
        eqN_two D.lg (D.lP + 1) (AttSeg.uD D C p.z) (X / 2 ^ D.ln), mul_assoc]
      rfl
    rw [hW]
    show _ * AttSeg.conB D (AttSeg.zi' D C p.z)
        (fun i' => AttSeg.qryV t b (X / 2 ^ D.ln / D.nBlk) (D.B * (X / 2 ^ D.ln % D.nBlk) + i')
        (X % 2 ^ D.ln)) *
      AttSeg.conB D (AttSeg.zj' D C p.z)
          (fun j' => AttSeg.keyV t (D.lamOf b) (X / 2 ^ D.ln / D.nBlk)
          (D.B * (X / 2 ^ D.ln % D.nBlk) + j') (X % 2 ^ D.ln)) = _
    ring
  refine (Finset.sum_congr rfl fun X _ => hsum X).trans ?_
  rw [sum_tail (D.lg + (D.lP + 1)) D.ln F, hF, ext_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  unfold scD
  rw [show D.ch = 2 ^ D.ln from rfl, Finset.mul_sum, Finset.mul_sum]

/-- The weighted sum of the gap's extensions on region D. -/
theorem gapD [scl : Scl] (hM : D.lM ≤ C.Dk) (ha : C.Dk ≤ C.a 0) :
    ∑ b ∈ range D.nb, AttSeg.wp D C p.z .d1 b *
        Blocks.ext D.lD (AttSeg.gp D t .D b) (AttSeg.uD D C p.z) =
      ∑ b ∈ range D.nb, AttSeg.wp D C p.z .d1 b *
          AttSeg.rd2 D (AttSeg.zgD D C p.z)
              (AttSeg.eqT D (AttSeg.cat (D.lP + 1) (AttSeg.zID D C p.z) (AttSeg.zi' D C p.z)))
              (AttSeg.mxV t b) -
        AttSeg.sumPhi D C p t .s6d +
        ((AttSeg.Om D : ℤ) : E) * AttSeg.LL D C p.z .d1 *
            (1 - AttSeg.LE D.lB (AttSeg.zj' D C p.z) (AttSeg.zi' D C p.z)) := by
  rw [ssD_eq]
  unfold AttSeg.LL
  simp only [gpD_ext D C p t hM ha, msD_eq D]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show _ * (AttSeg.rd2 D (AttSeg.zgD D C p.z)
      (AttSeg.eqT D (AttSeg.cat (D.lP + 1) (AttSeg.zID D C p.z) (AttSeg.zi' D C p.z)))
      (AttSeg.mxV t b) - _ + _) = _
  ring

end Inst.Model.AttSeg.KeyFormsExt
