-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/PublicForCompletenessAtHome.lean: PublicForCompleteness at the layout of the
goals' description, at all public files and every value of the readings. No premise.
-/
import VerifiableInference.Final.CompilerTheorems
import Johnson.Prover.At.HomeAt

set_option autoImplicit false
noncomputable section
open scoped ENNReal

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- the input there -/
local notation "ℌ" => Description.input (Description.reBound flashProveDescription b) Z allZeroDigest []
/-- the told record there -/
local notation "𝔗" => LayoutsByPublicReading.reBound (HonestTerms.T (theTerms placeHolderCoins) Z) (b Z)

/-- The layout of the description at a value of the readings. -/
@[reducible] def homeWiring (d : (𝔗).D) : HashLayout (ℌ).protocol (ℌ).offlineRoundSplits (ℌ).linkRoundSplits :=
  ⟨(ℌ).LeafBody, (ℌ).queryLayout, (𝔗).Sd d, (𝔗).cA d, (ℌ).fixedSample, (ℌ).compilerParameters, (ℌ).oracleCoding, (ℌ).keyCode, (ℌ).buildInstance⟩

set_option maxRecDepth 100000 in
/-- **All of PublicForCompleteness at the description, with no premise**, at any search limits. -/
theorem publicForCompleteness_home (d : (𝔗).D) (capT capL capB : ℕ → ℕ) :
    PublicForCompleteness (homeWiring b Z d) capT capL capB :=
  ⟨lawFit_home b Z d capT capL capB, wiresFit_home b Z d⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.homeWiring
#print axioms VerifiableInference.Compilation.publicForCompleteness_home
