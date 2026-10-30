-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Asks57.lean: two of the rows of
Johnson/Goal/Conditions/RowsAtTheRecord.lean, paid at the name.
`hext_row`: the row `VerifierAndGoals.AtTheName.Hext` is `hext_the` (Hext.lean). `meaning_row`: the row
`VerifierAndGoals.AtTheName.Meaning`, from `meaning_the` (Johnson/Goal/Conditions/SoundAtThe.lean) and
`lawful_ppAtFiles`. `one_extractor`: `theBound K` (AtBound.lean) and the name, where the goals read
it, have one extractor.
Limits. Two equations and a repacking: nothing on soundness. The rows `KeySound`, `EntrySound` and
`ProofSound` are not paid here (where they are paid, and how far: the head of
Johnson/Goal/TopOfThree.lean, limit (1)). The row `Carries` is paid in RowsAtTheRecord.lean itself.

-/
import Johnson.Goal.Description.AtName
import Johnson.Goal.Conditions.RowsAtTheRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve VerifierAndGoals.AtTheName
open VerifiableInference VerifiableInference.OnPublicFiles

theorem hext_row : VerifierAndGoals.AtTheName.Hext := hext_the

theorem meaning_row : VerifierAndGoals.AtTheName.Meaning :=
  fun Z _ i x' a x hb hw => ⟨lawful_ppAtFiles _ _, meaning_the Z i x' a x hb hw⟩

section
/- Lean compares these names and does not open them: without the marks a bare `rfl` runs into
Lean's limit. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

theorem one_extractor (K : TheCoins) (o : SecondHashFunctionType) :
    (theBound K o).extractor = (atSecondHashFunction theDescription).extractor :=
  ofBuilt (Q := fun D => (theBound K o).extractor = D.extractor) (by
    funext Z s commitment queryLog
    rfl)

end

end FlashProve

#print axioms FlashProve.hext_row
#print axioms FlashProve.meaning_row
#print axioms FlashProve.one_extractor
