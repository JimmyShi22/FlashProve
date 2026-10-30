-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/KeyDepthAtThe.lean: at the closed term `VerifierAndGoals.theDescription`: the depth of
the key's binding tree is 0 where the gate `protocolDataWellFormed` is open. Theorems.

Why. The key file's rule (`keySoundOfFullD_plain_at`, Johnson/Flat/Dec/PlainAtLetters.lean) asks `2
^ Tl.depthReqT * cS ≤ Tl.εs`. With the bound on a round's error at 2⁻¹ ^ 128 a proof wants that
factor to be 1. The row at the name (`VerifierAndGoals.AtTheName.KeySound`,
Johnson/Goal/Conditions/RowsAtTheRecord.lean) gives `InScope Z` and `protocolDataWellFormed (asDescriptionFiles Z)` alone, and
neither says that the depth is 0.

Main names.
  `depthReqT_the`: `((dataAtFiles flashProveData Z).inputFieldsAtReadings c m).depthReqT = 0`, from `protocolDataWellFormed`'s yes alone
    (`thePlan_oneLeaf`, Johnson/Goal/Description/PlanKey.lean: the frame's plan is the one of which
    the key file's description is made, and the key's seat asks that its parameter bytes are fewer
    than 2 ^ 64).
  `hc_the`: so `2 ^ depthReqT * cS ≤ εs` there is `cS ≤ εs`.

Limits. Two equations and one law on the planner, under `protocolDataWellFormed`'s yes; `protocolDataWellFormed` says yes at
the written copies by theorem (AtFullSide/Top/), as bytes by evaluation alone. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.LiveAtThe
import Johnson.Goal.Conditions.DepthsAtDescriptionDataAtFiles
import Johnson.Goal.Description.PlanKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace FlashProve
open VerifierAndGoals FlashProve VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat
open _root_.Iop (Dig)

/-- **At the name the key's binding tree has one leaf**, where the gate is open. -/
theorem depthReqT_the (Z : PublicFiles) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : Digest)
    (m : List (Dig 256)) : ((dataAtFiles flashProveData Z).inputFieldsAtReadings c m).depthReqT = 0 := by
  rw [depthReqT_tOf, g_built_live Z hl]
  exact thePlan_oneLeaf Z hl

/-- So the rule's premise on the shared chain's bound asks no factor there. -/
theorem hc_the (Z : PublicFiles) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (c : Digest) (m : List (Dig 256))
    (cS : ℝ≥0∞) (h : cS ≤ ((dataAtFiles flashProveData Z).inputFieldsAtReadings c m).εs) :
    ((2 ^ ((dataAtFiles flashProveData Z).inputFieldsAtReadings c m).depthReqT : ℕ) : ℝ≥0∞) * cS ≤
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c m).εs := by
  rw [depthReqT_the Z hl c m]
  simpa using h

end FlashProve

#print axioms FlashProve.depthReqT_the
#print axioms FlashProve.hc_the
