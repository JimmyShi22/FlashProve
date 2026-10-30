-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/LiveAtThe.lean: what ties an evaluation of protocolDataWellFormed
  (Johnson/Goal/Description/Live.lean) to the description's own letters: flashProveData has no code as a
  whole, so a
  harness evaluates protocolDataWellFormed, theKeyData, theProofData and thePlan; here: these are flashProveData's
  and,
  where protocolDataWellFormed says yes, dataAtFiles flashProveData's.
  theLay_live       flashProveData.live = protocolDataWellFormed := rfl
  g_built_live | dk_built_live | dp_built_live   where protocolDataWellFormed (asDescriptionFiles Z) = true: (dataAtFiles flashProveData
    Z).G | .DK | .DP = thePlan (asDescriptionFiles Z) | theKeyData (asDescriptionFiles Z) | theProofData (asDescriptionFiles Z)
Nothing on what protocolDataWellFormed says at any files: that is an evaluation. What protocolDataWellFormed's yes holds is said
  beside its text (theLive_frame | theLive_depth | theLive_full).
No soundness is claimed.
-/
import Johnson.Goal.Description.Lay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie OnBytes.K.Arm.Pub
open LPFD.Full (KF)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] theKeyData theProofData theDeadPlan thePlan

attribute [local irreducible] protocolDataWellFormed

theorem theLay_live : flashProveData.live = protocolDataWellFormed := by
  delta flashProveData
  rfl

theorem g_built_live (Z : PublicFiles) (h : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).G = thePlan (asDescriptionFiles Z) := by
  show flashProveData.filesParametersOrDefault (asDescriptionFiles Z) = _
  unfold DescriptionData.filesParametersOrDefault
  exact if_pos h

theorem dk_built_live (Z : PublicFiles) (h : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DK = theKeyData (asDescriptionFiles Z) := by
  show flashProveData.keyRoundsOrEmpty (asDescriptionFiles Z) = _
  unfold DescriptionData.keyRoundsOrEmpty
  exact if_pos h

theorem dp_built_live (Z : PublicFiles) (h : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DP = theProofData (asDescriptionFiles Z) := by
  show flashProveData.proofRoundsOrEmpty (asDescriptionFiles Z) = _
  unfold DescriptionData.proofRoundsOrEmpty
  exact if_pos h

end FlashProve

#print axioms FlashProve.theLay_live
#print axioms FlashProve.g_built_live
#print axioms FlashProve.dk_built_live
#print axioms FlashProve.dp_built_live
