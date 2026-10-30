-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/MakerReturnsAtLive.lean: where the public files are in scope, can be read and the
library's test on them says yes, the maker onlineProverFromPublicFiles returns at the filling of the honest prover.

  maker_returns   the head exists by head_exists_at_name; then atPure_returns_term

Limits.
- That onlineProverFromPublicFiles returns says nothing of what its prover plays.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.ReturnsAtAnyIndex
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.Desc.ProofFile.Honest.OpenHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput tableCoins)

/-- **The maker returns where the library's test says yes.** -/
theorem maker_returns (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (scope : VerifierAndGoals.InScope Z = true)
    (read : VerifierAndGoals.readFiles Z = .ok pp)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (OnlineProverParts.through id (tableCoins Z) matrixInput.dummy
        (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest)) = .ok A := by
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z scope read hl (P5J.owed_of_live hl)
  obtain ⟨A, hA, -⟩ := atPure_returns_term h hl OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest
  exact ⟨A, hA⟩

end AtFullSide.K12

#print axioms AtFullSide.K12.maker_returns
