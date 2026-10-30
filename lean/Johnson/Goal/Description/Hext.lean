-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Hext.lean: the extractor's row at the name. `hext_the`: the hypothesis
`hext` of `G8_theDescription` (JointD.lean), at the letters of Letters.lean: `flashProveData`'s extractor is
the told record's over `flashProveData`'s own family, then `thePhiO`. By unfolding (the told record reads no
extractor) and the settings' validity where the public files are read.

-/
import Johnson.Goal.Description.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
    theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF
      OnBytes.K.Arm.Pub.pub8
  FlashProve.thePlan FlashProve.theItem

theorem hext_the (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (_ : InScope Z = true) (hr : readFiles Z = .ok pp) :
    (dataAtFiles flashProveData Z).ext (settingsOfRead pp) = fun commitment queryLog =>
      (((dataAtFiles flashProveData Z).layoutsByPublicReading theC0 theM0).extractor commitment queryLog).bind
        (thePhiO Z (settingsOfRead pp) (valid_of_read hr)) := by
  funext commitment queryLog
  show theExtractor (asDescriptionFiles Z) (settingsOfRead pp) commitment queryLog = _
  unfold theExtractor
  refine congrArg₂ Option.bind rfl ?_
  funext M
  exact dif_pos (valid_of_read hr)

end FlashProve
