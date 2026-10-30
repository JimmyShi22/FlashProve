-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/ObjBitsProof.lean: the proofs of the statements of Cond/ObjBits.lean on the sum of the errors
of a list.

Terms: lean/GLOSSARY.md.
-/
import Cond.ObjBits

set_option autoImplicit false

namespace Iop
open scoped ENNReal

theorem Err.below_of_sumPr_le : ∀ {s : Shape} (ε : Err s) (c : ℝ≥0∞), ε.sumPr ≤ c → Err.Below ε c
  | [], _, _, _ => trivial
  | r :: _, (e, ε), c, h => by
    have h0 : (Fintype.card r.Chal : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have ht : (Fintype.card r.Chal : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    refine ⟨?_, Err.below_of_sumPr_le ε c (_root_.le_trans le_add_self h)⟩
    calc
      (e : ℝ≥0∞) = (e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞) * (Fintype.card r.Chal : ℝ≥0∞) :=
        (ENNReal.div_mul_cancel h0 ht).symm
      _ ≤ c * (Fintype.card r.Chal : ℝ≥0∞) := mul_le_mul' (_root_.le_trans le_self_add h) le_rfl

theorem Err.sumPr_app :
    ∀ {s t : Shape} (ε : Err s) (ε' : Err t), (Err.app ε ε').sumPr = ε.sumPr + ε'.sumPr
  | [], _, _, _ => (_root_.zero_add _).symm
  | r :: _, _, (e, ε), ε' => by
    show (e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞) + (Err.app ε ε').sumPr =
      (e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞) + ε.sumPr + ε'.sumPr
    rw [Err.sumPr_app ε ε', add_assoc]

variable {I X Wn : Type}

end Iop

noncomputable section

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open Compile.BatchLife (Sims)
open scoped ENNReal

theorem err_below_sumPr : Spec.err_below_sumPr := fun _ ε c h => Err.below_of_sumPr_le ε c h
theorem err_sumPr_app : Spec.err_sumPr_app := fun _ _ ε ε' => Err.sumPr_app ε ε'

theorem target_below_total : Spec.target_below_total := by
  intro C S P
  have hB : P.Below P.total := by
    refine ⟨Err.below_of_sumPr_le _ _ ?_,
      Err.below_of_sumPr_le _ _ ?_,
      Err.below_of_sumPr_le _ _ ?_,
      Err.below_of_sumPr_le _ _ ?_,
      Err.below_of_sumPr_le _ _ ?_⟩
    · exact le_trans le_self_add (le_trans le_self_add (le_trans le_self_add le_self_add))
    · exact le_trans le_add_self (le_trans le_self_add (le_trans le_self_add le_self_add))
    · exact le_trans le_add_self (le_trans le_self_add le_self_add)
    · exact le_trans le_add_self le_self_add
    · exact le_add_self
  refine ⟨hB,
    fun g =>
      ⟨Err.BelowG.of_below _ hB.wf,
        Err.BelowG.of_below _ hB.linOff,
        Err.BelowG.of_below _ hB.link,
        Err.BelowG.of_below _ hB.req,
        Err.BelowG.of_below _ hB.linOn⟩,
    fun r => ?_⟩
  show _ =
    (Err.app P.wf.err P.linOff.err).sumPr + P.link.err.sumPr + (Err.app P.req.err P.linOn.err).sumPr
  rw [Err.sumPr_app, Err.sumPr_app]
  unfold SubsR.Nums.total
  rw [add_assoc (P.wf.err.sumPr + P.linOff.err.sumPr + P.link.err.sumPr)]

theorem target_eps : Spec.target_eps := by
  intro Nn _ C S P b εs r lam D κ₀ n o c tC tP
  cases o <;> rfl

end TopC
