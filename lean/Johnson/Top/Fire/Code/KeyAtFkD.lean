-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyAtFkD.lean (`instKD` is `Key.keyInstanceOfOutOfDomainSample`, Johnson/Desc/Key/Slot.lean):  DOES THE FRAME's CORE, GENERAL IN THE INSTANCE's TYPE, TAKE THE SET OF DESCRIPTIONS MADE BY THE MAKER WITHOUT BUILD-TIME CODE, AT THAT MAKER's OWN TYPE OF A KEY FILE's INSTANCE (`Key.Xi`)?
Main names. `instKD`: the record as the key file's plain instance, at `Key.Xi` · `KeyOwedAtD A E := KeyCapOn instKD FkInScopeD A E` · `KeyLeadsOwedAtD A E rK := KeyLeadsOn instKD FkInScopeD A E rK` · `keySound_at_D` | `keySound_at_D_leads`: from each the key file's named hypothesis at every record of the frame's letters whose key's decision is the description's own behind a gate, one leaf: the tops of KeyAtFkZ.lean and KeyLeadsAtFkZ.lean (neither is in this library), over the new maker.
Limits. The two statements are OWED, not paid. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyLeadsRamp
import Johnson.Top.Fire.Code.KeyFkAtD
import Johnson.Desc.Key.Slot

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

open VerifiableInference.Desc.Key (Xi)

/-- The record as the key file's plain instance: `Key.keyInstanceOfOutOfDomainSample` ITSELF (Johnson/Desc/Key/Slot.lean), by which the seat's value in verify()'s text is laid. -/
abbrev instKD : RecFull → Xi := VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample

/-- **What is owed, in the rows' coin at the cap.** -/
def KeyOwedAtD {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) : Prop := KeyCapOn instKD FkInScopeD A E

/-- **What is owed, in the rule's own coin.** -/
def KeyLeadsOwedAtD {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) : Prop := KeyLeadsOn instKD FkInScopeD A E rK

theorem keySound_at_D {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (h : KeyOwedAtD A E)
    (Z : OnBytes.K.Pub) (cfg : ByteArray) (F : FileDescription Xi) (DK : WholeD)
    (hs : VerifierAndGoals.InScope ⟨Z.pol, Z.lay, Z.KL⟩ = true) (hcfg : cfg.size = 32) (hF : fkAtD Z cfg = .ok F) (hD : F.data "key file" = .ok (DK.at frS.P.T.a))
    {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
    {b : Bool} (er : runK = gatedFileDecision b (F.pull instKD).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hd : Tl.depthReqT = 0) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) :=
  keySound_on_cap instKD FkInScopeD A E h F DK ⟨Z, cfg, hs, hcfg, hF⟩ hD er Tl hd

theorem keySound_at_D_leads {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A)
    (Z : OnBytes.K.Pub) (cfg : ByteArray) (F : FileDescription Xi) (DK : WholeD)
    (hs : VerifierAndGoals.InScope ⟨Z.pol, Z.lay, Z.KL⟩ = true) (hcfg : cfg.size = 32) (hF : fkAtD Z cfg = .ok F) (hD : F.data "key file" = .ok (DK.at frS.P.T.a))
    {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
    {b : Bool} (er : runK = gatedFileDecision b (F.pull instKD).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (h : KeyLeadsOwedAtD A E rK) (hd : Tl.depthReqT = 0) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) :=
  keySound_on_leads instKD FkInScopeD A E F DK ⟨Z, cfg, hs, hcfg, hF⟩ hD er Tl h hd

end LPFD

#print axioms LPFD.KeyOwedAtD
#print axioms LPFD.keySound_at_D
#print axioms LPFD.keySound_at_D_leads
