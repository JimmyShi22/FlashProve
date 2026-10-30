-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/FrontRootAnsSide.lean: copies of `verifyAtKeyRoot`
(Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean), typed over the verifier's side of the object (`LHV`:
Hiop/RecSide.lean says what that is and why it is there).

Main name: `VRAV`.
The tie (`VRA_v`): `verifyAtKeyRoot` at L equals its copy here at `L.v`, at every argument. The proof of
`innerCompiledVerifier_eq` (Johnson/Top/InnerCompiledVerifierSide.lean) rests on it. If one of the two copies is changed
alone, this file no longer compiles: do not drop the tie in a clean-up.
Limits: definitions and this equation. Nothing on soundness.

-/
import Johnson.TypedOracleCompiler.RecCompile.FrontRootAns
import Johnson.TypedOracleCompiler.RecCompile.FrontRootSide
import Johnson.TypedOracleCompiler.RecCompile.CmsAnsSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

section RunV

variable {L : LHV X} {Bd : Type} {aT : RoundSplits L.test.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (carrierV L Bd aT aL)) (S : SeedV lam W.K L Bd aT aL)
  (cA : L.Ans → List (Dig lam)) (r₀ : L.Rec)

/-- The verifier at the key (root, record). -/
def VRAV (p : Params) (k : KeyRootV lam L) (x : X) (π : PrfRootV lam L aT aL) :
    TypedOracleComputation lam W.K (carrierV L Bd aT aL) Bool :=
  VCAV W S cA r₀ p (k.full π) x π.low

end RunV

/-! ## The tie -/

section Ties

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

theorem VRA_v (p : Params) (k : KeyRoot lam L) (x : X) (π : OfflineLinkOnlineProof lam L aT aL) :
    verifyAtKeyRoot W S cA r₀ p k x π =
      VRAV (L := L.v) W S.v cA r₀ p k.v x π.v :=
  VCA_v W S cA r₀ p (k.full π) x π.low

end Ties

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.VRA_v
