-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/MakerReturnsBase.lean: where the public files are in scope and the library's test on
them says yes, the maker returns at the base filling: so a law that takes the return at that filling
as a hypothesis is not empty there.

  maker_returns_base    at any index type whose named member is in range
  maker_returns_matrix  at the matrices

By what. The head: P5J.head_exists_at_name, P5J.owed_of_live. The return:
AtFullSide.K12.atPure_returns_fillW_at.

Limits.
- That the maker returns says nothing of what its prover plays.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K1.HeadAtReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifierAndGoals (asDescriptionFiles InScope)
open FlashProve (protocolDataWellFormed)

/-- **The maker returns at the base filling.** -/
theorem maker_returns_base {W₀ : Type} (Z : VerifierAndGoals.PublicFiles) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (range : I.inRange I.dummy = true)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A := by
  obtain ⟨pp, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  obtain ⟨A, hA, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h live I OnBytes.secondHashFunction S O range
  exact ⟨A, hA⟩

/-- **The maker returns at the base filling at the matrices.** -/
theorem maker_returns_matrix (Z : VerifierAndGoals.PublicFiles) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse ProofFile.Honest.Term.matrixInput OnBytes.secondHashFunction S O) = .ok A :=
  maker_returns_base Z _ S O ProofFile.Honest.Term.range_matrixInput scope live

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.maker_returns_base
#print axioms ProofFile.Honest.K1.maker_returns_matrix
