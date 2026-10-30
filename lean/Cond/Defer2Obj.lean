-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/Defer2Obj.lean: the formula `zetaT2`, beside `zetaT` of Cond/ObjBounds.lean, with the inner vertices
of the token trees and request trees at 2 λ bits (`muB2`, `hashSqBG2`: CompileK/Defer2Cost.lean).

Definitions, statements and proofs.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2Work
import CompileK.Defer2Cost
import CompileK.WideLang
import CompileK.KnowWidePass
import CompileK.Recompute
import CompileK.KnowLocal
import Cond.ObjBitsProof
import CompileK.WideZero
import Hiop.KnowWideRecompute
import Cond.ObjBounds

set_option autoImplicit false

noncomputable section

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open Compile.BatchLife (Sims)
open scoped ENNReal

/-- ζ, with the vertices at 2 λ (in `muB2` the entry xReq / 2^λ stays). -/
def zetaT2 {C : ConfigurationWithOutOfDomainSample} {S : SubsR C} {Nn : Type} [Inhabited Nn] (P : S.Nums) (r : C.Rec) {lam : ℕ}
    (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) :
    ℕ → ℕ → ℝ≥0∞ := fun t n' =>
  D.p.leaves * binTail n' D.p.leaves D.p.s1 +
    ((t : ℝ≥0∞) * muB2 D.W D.p n' + hashSqBG2 D.W D.p n') + workSq r D n' o +
    (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid)))

namespace Spec

/-- What ζ is. -/
def target_zeta2 : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b : ℕ) (εs : ℝ≥0∞)
      (r : C.Rec) (lam : ℕ) (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ)
      (o : Option (S.Wk Nn)) (c : ℝ≥0∞) (t n' : ℕ),
    (S.obj r).Opens D.no → S.N = 2 ^ D.ax.depthReq →
    zetaBGen (D.LO (SubsR.wkAt r o)) D.p (D.numsO (P.lh b εs) κ₀ n c (SubsR.wkAt r o))
        (hashTerms2 (D.WO (SubsR.wkAt r o)) D.p) t n' =
      zetaT2 P r D κ₀ n o t n'

end Spec

theorem target_zeta2 : Spec.target_zeta2 := by
  intro Nn _ C S P b εs r lam D κ₀ n o c t n' ho hN
  have base : ∀ M' : LH.Nums, M'.zT = κ₀ ^ n * P.wf.pHid →
      M'.zL = κ₀ ^ n * 0 → M'.zO = (κ₀ ^ n) ^ S.N * P.req.pHid →
      zetaBGen D.L D.p M' (hashTerms2 D.W D.p) t n' =
        D.p.leaves * binTail n' D.p.leaves D.p.s1 +
          ((t : ℝ≥0∞) * muB2 D.W D.p n' + hashSqBG2 D.W D.p n') +
          (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid))) := by
    intro M' h1 h2 h3
    show D.p.leaves * binTail n' D.p.leaves D.p.s1 +
        ((t : ℝ≥0∞) * muB2 D.W D.p n' + hashSqBG2 D.W D.p n') +
        (M'.zT + D.p.leaves * M'.zL + n' * ((S.N : ℝ≥0∞) * M'.zO)) = _
    rw [h1, h2, h3, mul_zero, mul_zero, add_zero]
  cases o with
  | none =>
    show zetaBGen D.L D.p (D.nums (P.lh b εs) κ₀ n) (hashTerms2 D.W D.p) t n' = _
    rw [base _ rfl rfl rfl]
    show _ = _ + 0 + _
    rw [add_zero]
  | some w =>
    show zetaBGen (D.L.grind Nn (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r))) D.p
        (D.numsWk (P.lh b εs) κ₀ n c)
        (hashTerms2 (D.W.grind w.Dg (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r))) D.p) t n' =
      _
    rw [Cost.zeta_work2 Nn _ _ lam D.L D.W w.Dg _ _ _ D.p (D.ok ho hN), base _ rfl rfl rfl]
    show _ + _ + _ +
        Cost.sqWork D.W w.Dg (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r)) D.p n' =
      _ + _ + Cost.sqWork D.W w.Dg (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r)) D.p n' + _
    exact add_right_comm _ _ _

/-- `zetaT2` is never above `zetaT0` (Cond/ObjBounds.lean). -/
theorem zetaT2_le {C : ConfigurationWithOutOfDomainSample} {S : SubsR C} {Nn : Type} [Inhabited Nn] (P : S.Nums) (r : C.Rec)
    {lam : ℕ} (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) (t n' : ℕ) :
    zetaT2 P r D κ₀ n o t n' ≤ zetaT0 P r D κ₀ n o t n' :=
  add_le_add (add_le_add (add_le_add le_rfl (hashTerms2_le D.W D.p t n')) le_rfl) le_rfl

end TopC
