-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsSide.lean: copies of `cmsLA`, `verifyLinkProof`
(Johnson/TypedOracleCompiler/RecCompile/LinkAns.lean), typed over the verifier's side of the object (`LHV`:
Hiop/RecSide.lean says what that is and why it is there).

Main names: `cmsLAV`, `vLAV`.
The ties (`cmsLA_v`, `vLA_v`): each of these at L equals its copy here at `L.v`, at every argument.
If one of the two copies is changed alone, this file no longer compiles: do not drop the ties in a
clean-up.
Limits: definitions and these equations. Nothing on soundness.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAns
import Johnson.TypedOracleCompiler.RecCompile.CmsSide

set_option autoImplicit false

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
  (cA : L.Ans → List (Dig lam))

/-- the list that a link's chain is handed: the two roots, then the answers of the two records -/
def cmsLAV (cm cm' : Dig lam) (an an' : L.Ans) : List (Dig lam) := cm :: cm' :: (cA an ++ cA an')

/-- The compiled Link, with the answers alone in the list. -/
def vLAV (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLV L aL)) :
    TypedOracleComputation lam W.K (carrierV L Bd aT aL) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.link (batLV L aL) (wLCV W) W.embL id (fun _ => none) W.embE W.depthReqL
    (cmsLAV cA cm cm' rec.2 rec'.2) (rec, rec') π

end RunV

/-! ## The ties -/

section Ties

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

theorem cmsLA_v (cm cm' : Dig lam) (an an' : L.OutOfDomainAnswer) :
    cmsLA (L := L) cA cm cm' an an' = cmsLAV (L := L.v) cA cm cm' an an' := rfl

theorem vLA_v (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    verifyLinkProof W cA p cm cm' rec rec' π = vLAV (L := L.v) W cA p cm cm' rec rec' π := rfl

end Ties

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.cmsLA_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.vLA_v
