-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/HeadAtBaseMaker.lean: the head at a return of the base maker (E2E/BaseMaker.lean), and
that the base maker returns.

  headAtReturn_baseMaker   headAtReturn_base at matrixInput
  baseMaker_returns        maker_returns_matrix

Limits. Those of AtFullSide/K1/HeadAtReturn.lean. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K1.MakerReturnsBase
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifierAndGoals (asDescriptionFiles InScope)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest.Term (baseMaker)

/-- **The head at a return of the base maker.** -/
theorem headAtReturn_baseMaker (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {A} (hA : baseMaker Z = .ok A) :
    ∃ H : ProofFile.Honest.FirstThread.HeadAtReturn Z A, A.F = H.description ∧
      ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G ∧
      H2U.placesOfMade A.Z.made = .ok H.places ∧ ProofFile.onlineFirstChainAt A.Z = .ok H.firstChain :=
  headAtReturn_base Z _ _ _ scope live hA

/-- **The base maker returns.** -/
theorem baseMaker_returns (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : ∃ A, baseMaker Z = .ok A :=
  maker_returns_matrix Z _ _ scope live

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.headAtReturn_baseMaker
#print axioms ProofFile.Honest.K1.baseMaker_returns
