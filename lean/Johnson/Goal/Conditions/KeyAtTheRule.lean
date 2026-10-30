-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/KeyAtTheRule.lean: at the closed term `VerifierAndGoals.theDescription`: the last call
for the key file, as a rule: the row `KeySound` (Johnson/Goal/Conditions/RowsAtTheRecord.lean) from
a statement at the name's own record which decides the key file by a description's own run behind an
open gate, has one leaf in the key's binding tree, and a bound of at least 2⁻¹ ^ 128. Two theorems.

Why. A top for the key file that is general in the frame's letters ends in just these facts on the
record. This file shows them at `(dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0`. `keySound_the_of_top` names no
description of a key file; `keySound_the_of_seat` rests on the one in the seat.

Main name. `keySound_the_of_top`: the row, from
  hrun: the named decision on the key file is the description's own run, at the files in scope at
    which `protocolDataWellFormed` says yes;
  top: the hypothesis at the name's record, under four facts: b is true; the decision is `gatedFileDecision b`
    of the run; the depth is 0; the bound is at least 2⁻¹ ^ 128.
b is `protocolDataWellFormed (asDescriptionFiles Z)` (`runK_the_at`, GatesAtThe.lean); the depth is 0 by `depthReqT_the`
(KeyDepthAtThe.lean); the bound is the record's own field.

`keySound_the_of_seat`: the same with hrun paid by the seat's own equation (`kseat_name`,
Johnson/Goal/Description/KeySeat.lean): `top` alone is left, and it is handed what that equation
gives of the description, and that the record's plan and key data are that description's maker's
plan and its own data.

Limits. A joining of statements: nothing of the key file's soundness is shown: `top` ends in the
row's own body. The row asks nothing where `protocolDataWellFormed` says no; it says yes at the written copies by
theorem (AtFullSide/Top/), as bytes by evaluation alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.RowsAtTheRecord
import Johnson.Goal.Conditions.GatesAtThe
import Johnson.Goal.Conditions.KeyDepthAtThe
import Johnson.Desc.Block
import Johnson.Goal.Description.KeySeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc

/-- **The row hole_keySound at the name, from a top at every record of the frame's letters.** -/
theorem keySound_the_of_top {XiK : Type} (F : OnBytes.K.Pub → FileDescription XiK) (instK : RecFull → XiK)
    (hrun : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      theKeyRun (asDescriptionFiles Z) = ((F (asDescriptionFiles Z)).pull instK).run)
    (top : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ b : Bool, b = true →
      (dataAtFiles flashProveData Z).runK = gatedFileDecision b ((F (asDescriptionFiles Z)).pull instK).run →
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).depthReqT = 0 →
      (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).εs →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0))) : KeySound :=
  fun Z hs hl =>
    top Z hs hl (protocolDataWellFormed (asDescriptionFiles Z)) hl (runK_the_at Z _ (hrun Z hs hl))
      (depthReqT_the Z hl theC0 theM0) ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).hε

/-- **The row from a top alone**: the description is the one that sits in the key file's seat. -/
theorem keySound_the_of_seat
    (top : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      ∀ X₀ m X N P,
      VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
      Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m →
      Key.descAt X₀ Z.lay Key.fixedDigest = .ok (Key.descriptionFromSource X N P) →
      (Key.descriptionFromSource X N P).planOk = true → (Key.descriptionFromSource X N P).wantedOk = true →
      (Key.descriptionFromSource X N P).owedOk = true →
      (∀ t ∈ Key.lawsAsk X₀ Z.lay m (Key.descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
      (Key.descriptionFromSource X N P).data "key file" = .ok (theKeyData (asDescriptionFiles Z)) →
      (dataAtFiles flashProveData Z).G = bigReq m.p → (dataAtFiles flashProveData Z).DK = theKeyData (asDescriptionFiles Z) →
      ∀ b : Bool, b = true →
      (dataAtFiles flashProveData Z).runK = gatedFileDecision b ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run →
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).depthReqT = 0 →
      (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).εs →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0))) : KeySound :=
  fun Z hs hl => by
    obtain ⟨X₀, m, X, N, P, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := kseat_name Z hl
    exact top Z hs hl X₀ m X N P h1 h2 h3 h4 h5 h6 h7 h8
      ((g_built_live Z hl).trans (thePlan_of_made h1 h2)) (dk_built_live Z hl)
      (protocolDataWellFormed (asDescriptionFiles Z)) hl
      (runK_the_at Z _ h9) (depthReqT_the Z hl theC0 theM0)
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).hε

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.keySound_the_of_top
#print axioms VerifierAndGoals.AtTheName.keySound_the_of_seat
