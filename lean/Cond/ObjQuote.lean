-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/ObjQuote.lean: the largest error of all five lists of an object with records (`Nums.maxAll`),
and how it bounds them.

Definitions, statements and proofs.

Limits: this file does not say that any bound is below 1.

Terms: lean/GLOSSARY.md.
-/
import Cond.ObjCtb
import Cond.ObjBounds
import Cond.ObjIndexMax

set_option autoImplicit false

noncomputable section

namespace Iop
open scoped ENNReal

theorem Err.maxPr_le_sumPr : ∀ {s : Shape} (ε : Err s), ε.maxPr ≤ ε.sumPr
  | [], _ => _root_.le_refl _
  | _ :: _, (_, ε) => _root_.max_le le_self_add (_root_.le_trans (Err.maxPr_le_sumPr ε) le_add_self)

theorem Err.maxPrG_le_maxPr : ∀ {s : Shape} (g : GBits s) (ε : Err s), ε.maxPrG g ≤ ε.maxPr
  | [], _, _ => _root_.le_refl _
  | r :: _, (b, g), (e, ε) => by
    refine max_le_max (ENNReal.div_le_div_left ?_ _) (Err.maxPrG_le_maxPr g ε)
    calc (Fintype.card r.Chal : ℝ≥0∞) = 1 * (Fintype.card r.Chal : ℝ≥0∞) := (one_mul _).symm
      _ ≤ (2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞) :=
        mul_le_mul' (one_le_pow₀ one_le_two) le_rfl

end Iop

namespace Hiop.SubsR
open Iop
open scoped ENNReal
variable {C : ConfigurationWithOutOfDomainSample} {S : SubsR C}

/-- The first count: the largest round error of the five lists, counting proof of work. -/
def Nums.maxAll {Nn : Type} (P : S.Nums) : Option (S.Wk Nn) → ℝ≥0∞
  | none =>
    max P.wf.err.maxPr
      (max P.linOff.err.maxPr (max P.link.err.maxPr (max P.req.err.maxPr P.linOn.err.maxPr)))
  | some w =>
    max (P.wf.err.maxPrG w.g.wf)
      (max (P.linOff.err.maxPrG w.g.linOff)
        (max (P.link.err.maxPrG w.g.link)
          (max (P.req.err.maxPrG w.g.req) (P.linOn.err.maxPrG w.g.linOn))))

theorem Nums.below_iff (P : S.Nums) (c : ℝ≥0∞) :
    P.Below c ↔ P.maxAll (none : Option (S.Wk Unit)) ≤ c := by
  show P.Below c ↔
    max P.wf.err.maxPr
        (max P.linOff.err.maxPr (max P.link.err.maxPr (max P.req.err.maxPr P.linOn.err.maxPr))) ≤ c
  rw [max_le_iff, max_le_iff, max_le_iff, max_le_iff, ← Err.below_iff_maxPr_le,
    ← Err.below_iff_maxPr_le, ← Err.below_iff_maxPr_le,
    ← Err.below_iff_maxPr_le, ← Err.below_iff_maxPr_le]
  exact ⟨fun h => ⟨h.wf, h.linOff, h.link, h.req, h.linOn⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

theorem Nums.belowG_iff {Nn : Type} (P : S.Nums) (w : S.Wk Nn) (c : ℝ≥0∞) :
    P.BelowG w.g c ↔ P.maxAll (some w) ≤ c := by
  show P.BelowG w.g c ↔
    max (P.wf.err.maxPrG w.g.wf)
        (max (P.linOff.err.maxPrG w.g.linOff)
          (max (P.link.err.maxPrG w.g.link)
            (max (P.req.err.maxPrG w.g.req) (P.linOn.err.maxPrG w.g.linOn)))) ≤ c
  rw [max_le_iff, max_le_iff, max_le_iff, max_le_iff, ← Err.belowG_iff_maxPrG_le,
    ← Err.belowG_iff_maxPrG_le, ← Err.belowG_iff_maxPrG_le,
    ← Err.belowG_iff_maxPrG_le, ← Err.belowG_iff_maxPrG_le]
  exact ⟨fun h => ⟨h.wf, h.linOff, h.link, h.req, h.linOn⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

end Hiop.SubsR

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open Compile.BatchLife (Sims)
open scoped ENNReal

/-- ε at the soundness number c. -/
def epsQ {Nn : Type} [Inhabited Nn] {C : ConfigurationWithOutOfDomainSample} {S : SubsR C} (r : C.Rec) {lam : ℕ}
    (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (o : Option (S.Wk Nn)) (c : ℝ≥0∞) :
    ℕ → ℕ → ℝ≥0∞ := fun tC tP =>
  ((tC + tP + tVB (D.WO (SubsR.wkAt r o)) + 1 : ℕ) : ℝ≥0∞) * (κ₀ ^ D.dr.K * c) + 2 * ((tC + tP + tVB (D.WO (SubsR.wkAt r o)) + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

namespace Spec

/-- States: "every round's error is at most c" says that the first count is at most c. -/
def target_maxAll : Prop :=
  ∀ (Nn : Type) (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (c : ℝ≥0∞),
    (P.Below c ↔ P.maxAll (none : Option (S.Wk Unit)) ≤ c) ∧
    ∀ w : S.Wk Nn, P.BelowG w.g c ↔ P.maxAll (some w) ≤ c

/-- States that the first count is at most the stricter one. -/
def target_maxAll_le : Prop :=
  ∀ (Nn : Type) (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (o : Option (S.Wk Nn)), P.maxAll o ≤ P.total

/-- States that one-block codings exist, under `Ctb S r` and for a type of nonces that is inhabited,
countable. -/
def target_quote_coding : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (r : C.Rec), Ctb S r →
    ∀ (lam : ℕ) (D : DataK (S.obj r) lam) (Nn : Type) [Inhabited Nn]
        [Countable Nn] (o : Option (S.Wk Nn)),
      ∃ m : OracleCoding (spec lam (D.WO (SubsR.wkAt r o)).K (D.LO (SubsR.wkAt r o))) lam,
        m.blocks OracleName.leaf = 1 ∧ m.blocks OracleName.node = 1

end Spec

theorem target_maxAll : Spec.target_maxAll := fun _ _ _ P c =>
  ⟨P.below_iff c, fun w => P.belowG_iff w c⟩

theorem target_maxAll_le : Spec.target_maxAll_le := by
  intro Nn C S P o
  have h1 : P.wf.err.sumPr ≤ P.total :=
    le_trans le_self_add (le_trans le_self_add (le_trans le_self_add le_self_add))
  have h2 : P.linOff.err.sumPr ≤ P.total :=
    le_trans le_add_self (le_trans le_self_add (le_trans le_self_add le_self_add))
  have h3 : P.link.err.sumPr ≤ P.total := le_trans le_add_self (le_trans le_self_add le_self_add)
  have h4 : P.req.err.sumPr ≤ P.total := le_trans le_add_self le_self_add
  have h5 : P.linOn.err.sumPr ≤ P.total := le_add_self
  cases o with
  | none =>
    exact max_le (le_trans (Err.maxPr_le_sumPr _) h1)
      (max_le (le_trans (Err.maxPr_le_sumPr _) h2)
        (max_le (le_trans (Err.maxPr_le_sumPr _) h3)
          (max_le (le_trans (Err.maxPr_le_sumPr _) h4) (le_trans (Err.maxPr_le_sumPr _) h5))))
  | some w =>
    exact max_le (le_trans (Err.maxPrG_le_maxPr _ _) (le_trans (Err.maxPr_le_sumPr _) h1))
      (max_le (le_trans (Err.maxPrG_le_maxPr _ _) (le_trans (Err.maxPr_le_sumPr _) h2))
        (max_le (le_trans (Err.maxPrG_le_maxPr _ _) (le_trans (Err.maxPr_le_sumPr _) h3))
          (max_le (le_trans (Err.maxPrG_le_maxPr _ _) (le_trans (Err.maxPr_le_sumPr _) h4))
            (le_trans (Err.maxPrG_le_maxPr _ _) (le_trans (Err.maxPr_le_sumPr _) h5)))))

theorem target_quote_coding : Spec.target_quote_coding := by
  intro C S r hc lam D Nn _ _ o
  obtain ⟨k1, k2⟩ :=
    countable_door Nn C.I C.X (S.obj r) lam D (SubsR.wkAt r o) hc.inst hc.sym hc.test hc.link hc.bat
  haveI := k1
  haveI := k2
  exact ⟨implAny lam (D.WO (SubsR.wkAt r o)).K (D.LO (SubsR.wkAt r o)),
    (exists_impl _ _ lam _ _).1,
    (exists_impl _ _ lam _ _).2⟩

end TopC
