-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/ZetaErr.lean: this folder's premise ZetaLe, one bound on the error term zetaW for
all values of the public reading, where the seven error numbers need not be 0.

What this file has (namespace OnBytes.FrontRoad).
zetaLe_withErrors: the premise ZetaLe of this folder's theorems on index privacy
(Johnson/FrontRoad/PremAt.lean). It is for public files Z in scope and every family F of parameters
and numbers over the values d of the public reading. Its premises are asked at every d. The number
of copies is M + 1. A copy bears at least s1 sessions. The limits on attempts are at most CT, CL,
CB. A leaf's salt has at least 256 free bits. The seven error numbers are at most zT, zL, zO, hT,
hL, hO, δ. The bound is boundZ (9 + CT + CL + CB) M t n plus the explicit sum (zT + (M + 1) · zL + n
· zO) + (hT + (M + 1) · hL + n · hO) + (M + 2) · δ for up to s1 requests, and the trivial bound
beyond (upTo, Johnson/FrontRoad/LaidSides.lean).

How it fits. It rests on zetaWithErrors (Johnson/FrontRoad/ZetaErrAtInput.lean), twelve_home
(E2E/LinkLaidPrivacy.lean) and zeta_told (E2E/LinkLaidTold.lean). A lemma on the way to index
privacy; not one of the release's goal statements.

Limits.
  All limits of Johnson/FrontRoad/ZetaErrAtInput.lean hold here. Above all: it gives no number for
      the seven error numbers, and a small bound says nothing on whether the prover is useful.
  The number of copies must be the same at every d, and one bound must serve each of the other
      numbers at all d.
Terms: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.
-/
import E2E.LinkLaidTold
import Johnson.FrontRoad.LaidSides
import Johnson.FrontRoad.ZetaErrAtInput

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid
open VerifiableInference.OnPublicFiles (InnerCompilerInput LayoutsByPublicReading)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (homeR homeT)
open AtPublicFiles.LinkLaid.Told (zeta_told)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

/-- **One bound on the error for all values of the public reading**, for a family of parameters and
numbers whose seven error numbers need not be 0. -/
theorem zetaLe_withErrors (b : PublicFiles → ℕ) (Z : PublicFiles) (scope : InScope Z = true)
    (F : SidesAt (homeT b Z)) (M s1 CT CL CB : ℕ) (zT zL zO hT hL hO δ : ℝ≥0∞)
    (hM : ∀ d, (F.a d).M = M) (hs : ∀ d, s1 ≤ (F.u d).s1) (cT : ∀ d i, (F.a d).capT i ≤ CT)
    (cL : ∀ d i, (F.a d).capL i ≤ CL) (cB : ∀ d i, (F.a d).capB i ≤ CB)
    (hℓ : ∀ d, 256 ≤ (F.c d).ℓ)
    (e : ∀ d, (F.u d).zT ≤ zT ∧ (F.u d).zL ≤ zL ∧ (F.u d).zO ≤ zO ∧ (F.u d).hT ≤ hT ∧
      (F.u d).hL ≤ hL ∧ (F.u d).hO ≤ hO ∧ (F.u d).δ ≤ δ) :
    ZetaLe F (fun _ => True) (upTo s1 fun t n =>
      boundZ (9 + CT + CL + CB) M t n +
        ((zT + ((M + 1 : ℕ) : ℝ≥0∞) * zL + (n : ℝ≥0∞) * zO) +
          (hT + ((M + 1 : ℕ) : ℝ≥0∞) * hL + (n : ℝ≥0∞) * hO) + ((M + 2 : ℕ) : ℝ≥0∞) * δ)) := by
  intro d _ t n
  by_cases hn : n ≤ s1
  · rw [upTo_of_le hn]
    refine (le_of_eq (congrFun (congrFun (zeta_told b Z d _ _ _) t) n)).trans ?_
    have h := zetaWithErrors (homeR b Z) (twelve_home b Z scope) (F.a d) (F.c d) (F.u d) t n CT CL
      CB (cT d) (cL d) (cB d) (hn.trans (hs d)) (hℓ d)
    rw [hM d] at h
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e d
    refine h.trans ?_
    gcongr
  · unfold upTo
    rw [if_neg hn]
    exact le_top

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.zetaLe_withErrors
