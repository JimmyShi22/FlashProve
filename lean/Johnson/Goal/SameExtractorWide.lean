-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/SameExtractorWide.lean: the extractor of the stand-in `theWide K W` IS that of `atSecondHashFunction
theDescription`, at every K and W: `same_extractor_wide`. Johnson/Goal/TopOfThreeBinding.lean has
the like for `theBound K` (`same_extractor_bound`) and says of `theWide K W` that it is not shown.
By `wide_extractor_bound`: re-bounding the number of coins and laying other honest terms turns no
letter of the extractor: the two stand-ins' extractors are one term.
Limits. An equation between two fields. Nothing on what the extractor finds.

-/
import Johnson.Goal.TopOfThreeBinding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve

/- Lean compares these names and does not open them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins) (W : WideCoins K)

/-- The two stand-ins have one extractor. -/
theorem wide_extractor_bound (o : SecondHashFunctionType) :
    (theWide K W o).extractor = (theBound K o).extractor := by
  funext Z s commitment queryLog
  rfl

/-- **The extractor of `theWide K W` is that of `atSecondHashFunction theDescription`.** -/
theorem same_extractor_wide (o : SecondHashFunctionType) :
    (theWide K W o).extractor = (atSecondHashFunction theDescription).extractor :=
  (wide_extractor_bound K W o).trans (same_extractor_bound K o)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.wide_extractor_bound
#print axioms VerifierAndGoals.AtTheName.same_extractor_wide
