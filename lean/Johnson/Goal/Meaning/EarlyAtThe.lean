-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/EarlyAtThe.lean: at the record of the rows on soundness
(Johnson/Goal/Conditions/RowsAtTheRecord.lean), where the test on numbers `protocolDataWellFormed` says yes, the
early part of a request is the request without its reply.

  `early_thePlanAt`: the field early of the plan that the frame lays (`thePlanAt o`,
    Johnson/Goal/Description/Plan.lean) is `reqWithoutReply`, at all public files and every o: in
    both arms.
  `early_the`: so is that of `(dataAtFiles flashProveData Z).G` where `protocolDataWellFormed (asDescriptionFiles Z)` says yes: there alone
    the row ProofSound asks anything.
User: whoever lays the rule of Johnson/Goal/Meaning/SpentAtPlain.lean, which stands at
early := reqWithoutReply, at the record.
Limits. Two equations. Where the test says no nothing is said.
-/
import Johnson.Goal.Conditions.RowsAtTheRecord
import Johnson.Flat.TiesAtReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat

theorem early_thePlanAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) :
    (thePlanAt o Zk).early = reqWithoutReply := by
  unfold thePlanAt filesParametersOrRefusalAt
  cases VerifiableInference.PlanWritten.plannedAtO o Zk.pol Zk.KL (some Zk.lay) fixedConfigurationDigest <;> rfl

theorem early_the (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).G.early = reqWithoutReply := by
  rw [builtS_live flashProveData Z live]
  exact early_thePlanAt OnBytes.secondHashFunction (asDescriptionFiles Z)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.early_thePlanAt
#print axioms VerifierAndGoals.AtTheName.early_the
