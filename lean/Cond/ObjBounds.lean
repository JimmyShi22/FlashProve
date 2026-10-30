-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/ObjBounds.lean: bounds and side conditions on the numbers of the five lists of an object with
records, written out as formulas.

Definitions, statements and proofs: unfolding; no new mathematics.

Main names: `Nums.alphaT`, `failO`, `epsT`, `zetaT`, `zetaT0`, `workSq`: the formulas. `TargetFit`,
`WorkFit`: the conditions on sizes and on the proof of work, written out.

Limits: this file says nothing on numerals. It does not say whether any parameters meet the
conditions.

Terms: lean/GLOSSARY.md.
-/
import Cond.ObjBitsProof
import CompileK.WideZero
import Hiop.KnowWideRecompute
import CompileK.WideLang
import CompileK.KnowWidePass
import CompileK.Recompute
import CompileK.KnowLocal
import CompileK.GrindCost
import CompileK.Defer2Work
import CompileK.Defer2Cost

set_option autoImplicit false

namespace Iop

theorem GBits.allLe_app {n : ℕ} :
    ∀ {s t : Shape} (g : GBits s) (g' : GBits t), (GBits.app g g').AllLe n ↔ g.AllLe n ∧ g'.AllLe n
  | [], _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _, (_, g), g' =>
    ⟨fun h => ⟨⟨h.1, ((GBits.allLe_app g g').1 h.2).1⟩, ((GBits.allLe_app g g').1 h.2).2⟩,
      fun h => ⟨h.1.1, (GBits.allLe_app g g').2 ⟨h.1.2, h.2⟩⟩⟩

end Iop

namespace Compile.Batch
open Iop
open scoped ENNReal

theorem gFail_app {Nn : Type} (D : GrData Nn) :
    ∀ {s t : Shape} (g : GBits s) (g' : GBits t), gFail D (GBits.app g g') = gFail D g + gFail D g'
  | [], _, _, _ => (zero_add _).symm
  | _ :: _, _, (b, g), g' => by
      show failBits D b + gFail D (GBits.app g g') = failBits D b + gFail D g + gFail D g'
      rw [gFail_app D g g', add_assoc]

theorem gFail_pull {Nn : Type} (D : GrData Nn) :
    ∀ {s : Shape} (σ : Samplers s) (g : GBits s), gFail D (g.pull σ) = gFail D g
  | [], _, _ => rfl
  | _ :: _, (_, σs), (b, g) => congrArg (failBits D b + ·) (gFail_pull D σs g)

end Compile.Batch

noncomputable section

namespace Hiop
open Iop Compile Compile.Batch
open scoped ENNReal

namespace SubsR
variable {C : ConfigurationWithOutOfDomainSample} {S : SubsR C}

/-- α without proof of work, in the parameters of the five lists; κ is the factor of the blocks of
one protocol. -/
def Nums.alphaT (P : S.Nums) (N : ℕ) (κ : ℝ≥0∞) : ℝ≥0∞ :=
  κ * (P.wf.pBad + P.wf.pHid + P.linOff.pBad) + κ * P.link.pBad +
    N * (κ * (P.req.pBad + P.req.pHid + P.linOn.pBad))

/-- The chances that a search fails, over the rounds of the five lists. -/
def Wk.fail {Nn : Type} (w : S.Wk Nn) (N : ℕ) : ℝ≥0∞ :=
  (gFail w.Dg w.g.wf + gFail w.Dg w.g.linOff) + gFail w.Dg w.g.link +
    N * (gFail w.Dg w.g.req + gFail w.Dg w.g.linOn)

def failO {Nn : Type} (N : ℕ) : Option (S.Wk Nn) → ℝ≥0∞
  | none => 0
  | some w => w.fail N

/-- The conditions on the proof of work, written out. -/
structure Wk.Fit {Nn : Type} (lam : ℕ) (w : S.Wk Nn) : Prop where
  read   : w.Dg.OK w.nb
  le     : w.nb ≤ lam
  wf     : w.g.wf.AllLe w.nb
  linOff : w.g.linOff.AllLe w.nb
  link   : w.g.link.AllLe w.nb
  req    : w.g.req.AllLe w.nb
  linOn  : w.g.linOn.AllLe w.nb

def WorkFit {Nn : Type} (lam : ℕ) : Option (S.Wk Nn) → Prop
  | none => True
  | some w => w.Fit lam

end SubsR
end Hiop

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open Compile.BatchLife (Sims)
open scoped ENNReal

section Defs
variable {C : ConfigurationWithOutOfDomainSample} {S : SubsR C}

/-- The conditions on sizes, written out. -/
structure TargetFit (P : S.Nums) (b : ℕ) (r : C.Rec) {lam : ℕ}
    (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ) : Prop where
  bias     : 1 ≤ κ₀
  samplers : D.dr.Good κ₀
  blocks   : D.dr.TotLe n
  opens    : (S.obj r).Opens D.no
  slots    : S.N = 2 ^ D.ax.depthReq
  fmt      : (S.obj r).onlineBatch.ann.Fmt
  /-- the first encoded index: the offline test's reads and those of all links -/
  budget0  : P.linOff.q + D.p.leaves * P.link.qpar ≤ b
  /-- a further encoded index: its link's reads and those of its sessions -/
  budgetJ  : P.link.qch + D.p.s1 * P.linOn.q ≤ b

/-- What proof of work adds to ζ. -/
def workSq {Nn : Type} [Inhabited Nn] (r : C.Rec) {lam : ℕ} (D : DataK (S.obj r) lam) (n' : ℕ) :
    Option (S.Wk Nn) → ℝ≥0∞
  | none => 0
  | some w => Cost.sqWork D.W w.Dg (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r)) D.p n'

/-- ε. -/
def epsT {Nn : Type} [Inhabited Nn] (εs : ℝ≥0∞) (r : C.Rec) {lam : ℕ} (D : DataK (S.obj r) lam)
    (κ₀ : ℝ≥0∞) (o : Option (S.Wk Nn)) (c : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞ := fun tC tP =>
  ((tC + tP + tVB (D.WO (SubsR.wkAt r o)) + 1 : ℕ) : ℝ≥0∞) *
      (κ₀ ^ D.dr.K * (if o.isSome then c else εs)) +
    2 * ((tC + tP + tVB (D.WO (SubsR.wkAt r o)) + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

/-- ζ: the inner vertices of the token trees and request trees at 2 λ bits (`muB2`, `hashSqBG2`:
CompileK/Defer2Cost.lean; in `muB2` the entry xReq / 2^λ stays; exactly: the head of that file). -/
def zetaT {Nn : Type} [Inhabited Nn] (P : S.Nums) (r : C.Rec) {lam : ℕ} (D : DataK (S.obj r) lam)
    (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) : ℕ → ℕ → ℝ≥0∞ := fun t n' =>
  D.p.leaves * binTail n' D.p.leaves D.p.s1 +
    ((t : ℝ≥0∞) * muB2 D.W D.p n' + hashSqBG2 D.W D.p n') + workSq r D n' o +
    (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid)))

/-- ζ with `muB`, `hashSqBG` where `zetaT` has `muB2`, `hashSqBG2`.
-/
def zetaT0 {Nn : Type} [Inhabited Nn] (P : S.Nums) (r : C.Rec) {lam : ℕ} (D : DataK (S.obj r) lam)
    (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) : ℕ → ℕ → ℝ≥0∞ := fun t n' =>
  D.p.leaves * binTail n' D.p.leaves D.p.s1 + ((t : ℝ≥0∞) * muB D.W D.p n' + hashSqBG D.W D.p n') +
    workSq r D n' o + (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid)))

end Defs

namespace Spec

/-- What α is. -/
def target_alpha : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b : ℕ) (εs : ℝ≥0∞)
      (r : C.Rec) (lam : ℕ) (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ)
      (o : Option (S.Wk Nn)) (c : ℝ≥0∞),
    (S.obj r).Opens D.no → S.N = 2 ^ D.ax.depthReq →
    alphaBG (D.WO (SubsR.wkAt r o)) (D.numsO (P.lh b εs) κ₀ n c (SubsR.wkAt r o)) =
      P.alphaT S.N (κ₀ ^ n) + SubsR.failO S.N o

/-- What ζ is. -/
def target_zeta : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b : ℕ) (εs : ℝ≥0∞)
      (r : C.Rec) (lam : ℕ) (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ)
      (o : Option (S.Wk Nn)) (c : ℝ≥0∞) (t n' : ℕ),
    (S.obj r).Opens D.no → S.N = 2 ^ D.ax.depthReq →
    zetaBGen (D.LO (SubsR.wkAt r o)) D.p (D.numsO (P.lh b εs) κ₀ n c (SubsR.wkAt r o))
        (hashTerms2 (D.WO (SubsR.wkAt r o)) D.p) t n' =
      zetaT P r D κ₀ n o t n'

/-- What `zetaT0` is. -/
def target_zeta0 : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b : ℕ) (εs : ℝ≥0∞)
      (r : C.Rec) (lam : ℕ) (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ)
      (o : Option (S.Wk Nn)) (c : ℝ≥0∞) (t n' : ℕ),
    (S.obj r).Opens D.no → S.N = 2 ^ D.ax.depthReq →
    zetaBGen (D.LO (SubsR.wkAt r o)) D.p (D.numsO (P.lh b εs) κ₀ n c (SubsR.wkAt r o))
        (hashTermsBGTot (D.WO (SubsR.wkAt r o)) D.p) t n' =
      zetaT0 P r D κ₀ n o t n'

/-- States that the compiler's conditions on numbers and formats are the named conditions. -/
def target_fit_iff : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b : ℕ) (εs : ℝ≥0∞) (r : C.Rec) (lam : ℕ)
      (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ),
    FitK D (P.lh b εs) κ₀ n ↔ TargetFit P b r D κ₀ n

def target_workFit_iff : Prop :=
  ∀ (Nn : Type) (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (r : C.Rec) (lam : ℕ) (o : Option (S.Wk Nn)),
    FitO lam (SubsR.wkAt r o) ↔ SubsR.WorkFit lam o

end Spec

theorem target_alpha : Spec.target_alpha := by
  intro Nn _ C S P b εs r lam D κ₀ n o c ho hN
  cases o with
  | none =>
    show alphaBG D.W (D.nums (P.lh b εs) κ₀ n) = _
    rw [alphaBG_data D ho hN]
    exact (add_zero _).symm
  | some w =>
    show alphaBG (D.W.grind w.Dg (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r)))
        (D.numsWk (P.lh b εs) κ₀ n c) = _
    rw [alphaBG_grind,
      show gFail w.Dg (D.gTd (w.at r)) = gFail w.Dg w.g.wf + gFail w.Dg w.g.linOff
        from (gFail_pull w.Dg _ _).trans (gFail_app w.Dg w.g.wf w.g.linOff),
      show gFail w.Dg (D.gLd (w.at r)) = gFail w.Dg w.g.link from gFail_pull w.Dg _ _,
      show gFail w.Dg (D.gBd (w.at r)) = gFail w.Dg w.g.req + gFail w.Dg w.g.linOn
        from (gFail_pull w.Dg _ _).trans (gFail_app w.Dg w.g.req w.g.linOn)]
    rfl

theorem target_zeta : Spec.target_zeta := by
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

theorem target_zeta0 : Spec.target_zeta0 := by
  intro Nn _ C S P b εs r lam D κ₀ n o c t n' ho hN
  have base : ∀ M' : LH.Nums, M'.zT = κ₀ ^ n * P.wf.pHid →
      M'.zL = κ₀ ^ n * 0 → M'.zO = (κ₀ ^ n) ^ S.N * P.req.pHid →
      zetaBGen D.L D.p M' (hashTermsBGTot D.W D.p) t n' =
        D.p.leaves * binTail n' D.p.leaves D.p.s1 +
          ((t : ℝ≥0∞) * muB D.W D.p n' + hashSqBG D.W D.p n') +
          (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid))) := by
    intro M' h1 h2 h3
    show D.p.leaves * binTail n' D.p.leaves D.p.s1 +
        ((t : ℝ≥0∞) * muB D.W D.p n' + hashSqBG D.W D.p n') +
        (M'.zT + D.p.leaves * M'.zL + n' * ((S.N : ℝ≥0∞) * M'.zO)) = _
    rw [h1, h2, h3, mul_zero, mul_zero, add_zero]
  cases o with
  | none =>
    show zetaBGen D.L D.p (D.nums (P.lh b εs) κ₀ n) (hashTermsBGTot D.W D.p) t n' = _
    rw [base _ rfl rfl rfl]
    show _ = _ + 0 + _
    rw [add_zero]
  | some w =>
    show zetaBGen (D.L.grind Nn (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r))) D.p
        (D.numsWk (P.lh b εs) κ₀ n c)
        (hashTermsBGTot (D.W.grind w.Dg (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r))) D.p)
        t n' = _
    rw [Cost.zeta_work Nn _ _ lam D.L D.W w.Dg _ _ _ D.p (D.ok ho hN), base _ rfl rfl rfl]
    show _ + _ + _ +
        Cost.sqWork D.W w.Dg (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r)) D.p n' =
      _ + _ + Cost.sqWork D.W w.Dg (D.gTd (w.at r)) (D.gLd (w.at r)) (D.gBd (w.at r)) D.p n' + _
    exact add_right_comm _ _ _

theorem target_fit_iff : Spec.target_fit_iff := fun _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => ⟨h.one_le, h.good, h.totLe, h.opens, h.slots, h.fmt, h.budget.1, h.budget.2⟩,
    fun h => ⟨h.bias, h.samplers, h.blocks, h.opens, h.slots, h.fmt, ⟨h.budget0, h.budgetJ⟩⟩⟩

theorem target_workFit_iff : Spec.target_workFit_iff := by
  intro Nn C S r lam o
  cases o with
  | none => exact Iff.rfl
  | some w =>
    constructor
    · intro h
      have h' : FitWk lam (w.at r) := h
      exact ⟨h'.read, h'.le,
        ((GBits.allLe_app w.g.wf w.g.linOff).1 h'.allT).1,
        ((GBits.allLe_app w.g.wf w.g.linOff).1 h'.allT).2,
        h'.allL,
        ((GBits.allLe_app w.g.req w.g.linOn).1 h'.allB).1,
        ((GBits.allLe_app w.g.req w.g.linOn).1 h'.allB).2⟩
    · intro h
      have h' : w.Fit lam := h
      exact (⟨h'.read, h'.le,
        (GBits.allLe_app w.g.wf w.g.linOff).2 ⟨h'.wf, h'.linOff⟩,
        h'.link,
        (GBits.allLe_app w.g.req w.g.linOn).2 ⟨h'.req, h'.linOn⟩⟩ : FitWk lam (w.at r))

end TopC
