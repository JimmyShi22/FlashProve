-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/NeverWhole.lean: where the key file's or the proof file's decision never accepts,
the compiled verifier rejects at EVERY typed proof and every hash function.
Johnson/Goal/Tie/NeverEvery.lean has this for the copy's file's decision. Here are the other two.
`vBAV_never`, `vTAV_never`: the proof file's and the key file's arm: by `verifyBS_never`
(NeverEvery.lean), which is general in the slot.
`verifyVDet_never_proof`, `verifyVDet_never_key`; `innerCompiledVerifier_never_proof`, `innerCompiledVerifier_never_key`: so
the whole verifier, at the verifier's side and at the input: by `VRAV_det`: the value is a
conjunction in which each arm stands.
`innerCompiledVerifierAtFullSize_never_proof`, `innerCompiledVerifierAtFullSize_never_key`: at the frame's letters, from
`wholeIOR_never` (Johnson/Flat/FailsClosed.lean).
Limits. Of use by contraposition: an accept shows that each decision accepts somewhere. Nothing on
where. Nothing on soundness.

-/
import Johnson.Goal.Tie.NeverEvery

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Cms
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {lam : ℕ} {L : LHV X} {Bd : Type} {aT : RoundSplits L.test.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (carrierV L Bd aT aL))
  (cA : L.Ans → List (Dig lam)) (r₀ : L.Rec) (p : Params)
  (F : Fam (typedOracleFamily lam W.K (carrierV L Bd aT aL)))

/-- The proof file's arm. -/
theorem vBAV_never (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.bat)
    (never : ∀ x y τ, L.bat.loc.accept x y τ = false) :
    (vBAV W cA r₀ p cm x rec π).det F = false :=
  verifyBS_never p.sMT p.sFS Tag.onl L.bat (wBCV W) W.embB id (xinBAV r₀) W.embE W.depthReq
    (cmsBAV cA cm rec.2) (x, rec) π (fun y τ => never (x, rec) y τ) F

/-- The key file's arm. -/
theorem vTAV_never (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTV L aT))
    (never : ∀ x y τ, L.test.accept x y τ = false) :
    (vTAV W cA p cm rec π).det F = false :=
  verifyBS_never p.sMT p.sFS Tag.test (batTV L aT) (wTCV W) W.embT id (fun _ => none) W.embE
    W.depthReqT (cmsTAV cA cm rec.2) rec π (fun y τ => never rec y τ) F

end TypedOracleCompiler.Compile.Batch.Cms

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- At the verifier's side: the proof file's decision. -/
theorem verifyVDet_never_proof (v : InputV) (never : ∀ x y τ, v.L.bat.loc.accept x y τ = false)
    (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : List Token × (KeyRootV 256 v.L × PrfRootV 256 v.L v.aT v.aL)) :
    verifyVDet v hash commitment prompt output proof = false := by
  unfold verifyVDet
  split
  · split
    · split
      · rw [VRAV_det]
        split
        · rw [vBAV_never _ _ _ _ _ _ _ _ _ never]
          simp
        · rfl
      · rfl
    · rfl
  · rfl

/-- At the verifier's side: the key file's decision. -/
theorem verifyVDet_never_key (v : InputV) (never : ∀ x y τ, v.L.test.accept x y τ = false)
    (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : List Token × (KeyRootV 256 v.L × PrfRootV 256 v.L v.aT v.aL)) :
    verifyVDet v hash commitment prompt output proof = false := by
  unfold verifyVDet
  split
  · split
    · split
      · rw [VRAV_det]
        split
        · rw [vTAV_never _ _ _ _ _ _ _ never]
          simp
        · rfl
      · rfl
    · rfl
  · rfl

/-- **At the input: reject, at every typed proof and every hash function**: the proof file's. -/
theorem innerCompiledVerifier_never_proof (r : InnerCompilerInput)
    (never : ∀ x y τ, r.protocol.v.bat.loc.accept x y τ = false) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (q : List Token × (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits)) :
    (innerCompiledVerifier r commitment prompt output q).evaluate hash = false := by
  have e : q = r.back (q.1, q.2.1.v, q.2.2.v) := rfl
  rw [e, ← verifyV_toInputV, verifyVDet_is]
  exact verifyVDet_never_proof r.toInputV never hash _ _ _ _

/-- The key file's. -/
theorem innerCompiledVerifier_never_key (r : InnerCompilerInput) (never : ∀ x y τ, r.protocol.v.test.accept x y τ = false)
    (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (q : List Token × (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits)) :
    (innerCompiledVerifier r commitment prompt output q).evaluate hash = false := by
  have e : q = r.back (q.1, q.2.1.v, q.2.2.v) := rfl
  rw [e, ← verifyV_toInputV, verifyVDet_is]
  exact verifyVDet_never_key r.toInputV never hash _ _ _ _

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}

/-- **At the frame's letters: the proof file's decision.** -/
theorem innerCompiledVerifierAtFullSize_never_proof (never : ∀ x v₁ v₂ v₃, runP x v₁ v₂ v₃ = false)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (q : List Token × (KeyRoot 256 (innerCompilerInputAtFullSize T).protocol ×
      OfflineLinkOnlineProof 256 (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits (innerCompilerInputAtFullSize T).linkRoundSplits)) :
    (innerCompiledVerifier (innerCompilerInputAtFullSize T) commitment prompt output q).evaluate hash = false :=
  innerCompiledVerifier_never_proof _
    (fun x y τ => wholeIOR_never (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP
      never x y τ) hash _ _ _ q

/-- **At the frame's letters: the key file's decision.** -/
theorem innerCompiledVerifierAtFullSize_never_key (never : ∀ r v₁ v₂ v₃, runK r v₁ v₂ v₃ = false)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (q : List Token × (KeyRoot 256 (innerCompilerInputAtFullSize T).protocol ×
      OfflineLinkOnlineProof 256 (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits (innerCompilerInputAtFullSize T).linkRoundSplits)) :
    (innerCompiledVerifier (innerCompilerInputAtFullSize T) commitment prompt output q).evaluate hash = false :=
  innerCompiledVerifier_never_key _
    (fun x y τ => wholeIOR_never (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK
      never x y τ) hash _ _ _ q

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierAtFullSize_never_proof
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierAtFullSize_never_key
