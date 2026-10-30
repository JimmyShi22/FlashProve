-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/CmsAnsSide.lean: copies of `cmsTA`, `cmsBA`, `xinBA`, `verifyOfflineProof`, `verifyOnlineProof`, `verifyAtFullKey`
(Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean), typed over the verifier's side of the object (`LHV`:
Hiop/RecSide.lean says what that is and why it is there).

Main names: `cmsTAV`, `cmsBAV`, `xinBAV`, `vTAV`, `vBAV`, `VCAV`.
The ties (`cmsTA_v`, `cmsBA_v`, `xinBA_v`, `vTA_v`, `vBA_v`, `VCA_v`): each of these at L equals its
copy here at `L.v`, at every argument. The proof of `innerCompiledVerifier_eq` (Johnson/Top/InnerCompiledVerifierSide.lean)
rests on `VCA_v`. If one of the two copies is changed alone, this file no longer compiles: do not
drop the ties in a clean-up.
Limits: definitions and these equations. Nothing on soundness.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAns
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsSide

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
  (cA : L.Ans → List (Dig lam)) (r₀ : L.Rec)

/-- the list that the key's chain is handed: the root, then the record's answers -/
def cmsTAV (cm : Dig lam) (an : L.Ans) : List (Dig lam) := cm :: cA an

/-- the list that a session's chain is handed: the root (twice), then the record's answers -/
def cmsBAV (cm : Dig lam) (an : L.Ans) : List (Dig lam) := cm :: cm :: cA an

/-- the session's request: the instance, with a fixed record in the record's place -/
def xinBAV (a : X × L.Rec) : Option L.XC := some (some a.1, r₀, r₀)

def vTAV (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTV L aT)) :
    TypedOracleComputation lam W.K (carrierV L Bd aT aL) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.test (batTV L aT) (wTCV W) W.embT id (fun _ => none) W.embE W.depthReqT
    (cmsTAV cA cm rec.2) rec π

def vBAV (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.bat) :
    TypedOracleComputation lam W.K (carrierV L Bd aT aL) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.onl L.bat (wBCV W) W.embB id (xinBAV r₀) W.embE W.depthReq
    (cmsBAV cA cm rec.2) (x, rec) π

/-- The verifier: `VC` (Cms.lean) with the three compiled verifiers at the answers alone. -/
def VCAV (p : Params) (v : KeyCV lam L aT aL) (x : X) (π : PrfCV lam L) :
    TypedOracleComputation lam W.K (carrierV L Bd aT aL) Bool :=
  match v.piT, v.links[π.leaf]?, π.piB with
  | some πT, some (cmj, recj, some πL), some πB =>
      (seedIsV W S v.cm v.rcd.1).bind fun s0 =>
      (seedIsV W S cmj recj.1).bind fun sj =>
      (vTAV W cA p v.cm v.rcd πT).bind fun a =>
      (vLAV W cA p v.cm cmj v.rcd recj πL).bind fun b =>
      (vBAV W cA r₀ p cmj x recj πB).bind fun c =>
      OComp.pure (S.num π.copy πB.plains && s0 && sj && a && b && c)
  | _, _, _ => OComp.pure false

end RunV

/-! ## The ties -/

section Ties

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

theorem cmsTA_v (cm : Dig lam) (an : L.OutOfDomainAnswer) :
    cmsTA (L := L) cA cm an = cmsTAV (L := L.v) cA cm an := rfl

theorem cmsBA_v (cm : Dig lam) (an : L.OutOfDomainAnswer) :
    cmsBA (L := L) cA cm an = cmsBAV (L := L.v) cA cm an := rfl

theorem xinBA_v (a : X × L.Rec) : xinBA (L := L) r₀ a = xinBAV (L := L.v) r₀ a := rfl

theorem vTA_v (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    verifyOfflineProof W cA p cm rec π = vTAV (L := L.v) W cA p cm rec π := rfl

theorem vBA_v (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    verifyOnlineProof W cA r₀ p cm x rec π = vBAV (L := L.v) W cA r₀ p cm x rec π := rfl

theorem VCA_v (p : Params) (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L) :
    verifyAtFullKey W S cA r₀ p v x π =
      VCAV (L := L.v) W S.v cA r₀ p v.v x π.v :=
  by delta verifyAtFullKey VCAV verifyAtFullKey.match_1 VCAV.match_1; rfl

end Ties

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.cmsTA_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.cmsBA_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.xinBA_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.vTA_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.vBA_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.VCA_v
