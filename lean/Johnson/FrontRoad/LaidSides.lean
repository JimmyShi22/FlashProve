-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/LaidSides.lean: the parameters at which the statements of
Johnson/FrontRoad/LaidIdSpec.lean are made, and the form of their bound. Definitions.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
  laidSides   for the family homeT b Z: at every value d of the public reading the same parameters.
      The honest side is laidAt (E2E/LinkLaidPrivacy.lean): its link prover is the explicit prover
      explicitLinkProver b Z (Johnson/LinkSim/AtHome/), and its provers for the first table and for the
      sessions are placeholder provers, which send fixed messages. The simulators are the explicit
      one for the link and the fixed ones for the other two sub-protocols. No out-of-domain seed is
      set aside.
  upTo s1 f   the bound f for up to s1 requests, and the trivial bound ⊤ beyond. upTo_of_le: its
      value for up to s1 requests.

How it fits. Johnson/FrontRoad/LaidIdSpec.lean names both in its statements.
Johnson/FrontRoad/LaidAll.lean proves that laidSides satisfies the premises of index privacy at
every d. Not among the release's goal statements.

Limits. Definitions alone. A bound of 1 or more is met by every scheme, so a statement with the
bound upTo s1 f bounds nothing beyond s1 requests.
-/
import E2E.LinkLaidPrivacy
import Johnson.Goal.Conditions.HomeAtWider
import Johnson.FrontRoad.PremAt

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput LayoutsByPublicReading)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (flashProveData homeR homeT flashProveDescription allZeroDigest)

/-- The bound f for up to s1 requests; beyond that the trivial bound. -/
def upTo (s1 : ℕ) (f : ℕ → ℕ → ℝ≥0∞) (t n : ℕ) : ℝ≥0∞ := if n ≤ s1 then f t n else ⊤

theorem upTo_of_le {s1 : ℕ} {f : ℕ → ℕ → ℝ≥0∞} {t n : ℕ} (h : n ≤ s1) : upTo s1 f t n = f t n :=
  if_pos h

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles) (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
  (E : BitsE b Z b₀ M ℓ ℓr capT capL capB)

/-- The parameters, the same at every d: the honest side laidAt, the explicit simulator for the
link and the fixed ones for the other two sub-protocols, no out-of-domain seed set aside. -/
def laidSides (i₀ : (homeR b Z).Index) : SidesAt (homeT b Z) where
  a := fun _ => laidAt b Z b₀ M ℓ ℓr capT capL capB E
  Sm := fun _ => fitSims (fixedSims (homeR b Z).protocol)
  Gs := fun _ _ => True
  c := fun _ => coinNums (homeR b Z) b₀ ℓ ℓr
  u := fun _ => fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)
  i₀ := fun _ => i₀

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.upTo
#print axioms OnBytes.FrontRoad.laidSides
