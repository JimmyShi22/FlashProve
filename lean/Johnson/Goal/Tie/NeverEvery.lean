-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/NeverEvery.lean: where the entry file's decision never says yes, the compiled
verifier says no at EVERY typed proof and every hash function.
`verifyBS_never`: the compiled verifier of one slot says no where its protocol's decision says no
to all at the instance: by its text: the decision is the last conjunct. `vLAV_never`: so the
entry's arm. `verifyVDet_never`, `innerCompiledVerifier_never_link`: so the whole verifier, at the verifier's
side and at the input: by `VRAV_det` (the value at every key and every proof),
`verifyVDet_is` and `verifyV_toInputV`; every typed proof is the way back of its own verifier's
side. `innerCompiledVerifierAtFullSize_never`: at the frame's letters, from `linkW_never`.
Why. The laws of Johnson/Goal/Description/Dead.lean go through the fast form, which is stated at
typed proofs that are laid of file forms; a parser of the goals may return any typed proof.
Limits. True where a gate is shut, and of use for the branch that refuses alone. It leans on the
entry's decision alone: nothing is said where that one can say yes and the other two cannot. At the
description's own letters, in scope and at the format's second hash function, no files are known at
which the gate is shut. Nothing on soundness.

-/
import Johnson.Top.InnerCompiledVerifierBack
import Johnson.Top.Fire.Code.VerifyVDetProbe
import Johnson.Top.Fire.Code.VCAVDet
import Johnson.Flat.Dec.FailsClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- **The compiled verifier of one slot says no where the decision says no to all.** -/
theorem verifyBS_never (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (never : ∀ y τ, Q.loc.accept x y τ = false) (F : Fam (typedOracleFamily lam K L)) :
    (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det F = false := by
  unfold verifyOneProtocol
  rw [OComp.det_bind]
  cases (recomputeChainOfProof t Q wq embP xin cms x π).det F with
  | none => rfl
  | some r =>
    obtain ⟨ρ, rts, ph⟩ := r
    dsimp only
    split
    · unfold checkPrunedOpenings
      split
      · split
        · unfold afterF
          simp only [OComp.det_bind]
          show (_ && _ && Q.loc.accept x _ _) = false
          rw [never, Bool.and_false]
        · rfl
      · rfl
    · rfl

end TypedOracleCompiler.Compile.Batch

namespace TypedOracleCompiler.Compile.Batch.Cms
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {lam : ℕ} {L : LHV X} {Bd : Type} {aT : RoundSplits L.test.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (carrierV L Bd aT aL))
  (cA : L.Ans → List (Dig lam)) (p : Params)
  (F : Fam (typedOracleFamily lam W.K (carrierV L Bd aT aL)))

/-- The entry's arm. -/
theorem vLAV_never (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLV L aL))
    (never : ∀ x y τ, L.link.accept x y τ = false) :
    (vLAV W cA p cm cm' rec rec' π).det F = false :=
  verifyBS_never p.sMT p.sFS Tag.link (batLV L aL) (wLCV W) W.embL id (fun _ => none) W.embE
    W.depthReqL (cmsLAV cA cm cm' rec.2 rec'.2) (rec, rec') π (fun y τ => never (rec, rec') y τ) F

end TypedOracleCompiler.Compile.Batch.Cms

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- At the verifier's side. -/
theorem verifyVDet_never (v : InputV) (never : ∀ x y τ, v.L.link.accept x y τ = false)
    (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : List Token × (KeyRootV 256 v.L × PrfRootV 256 v.L v.aT v.aL)) :
    verifyVDet v hash commitment prompt output proof = false := by
  unfold verifyVDet
  split
  · split
    · split
      · rw [VRAV_det]
        split
        · rw [vLAV_never _ _ _ _ _ _ _ _ _ never]
          simp
        · rfl
      · rfl
    · rfl
  · rfl

/-- **At the input: no, at every typed proof and every hash function.** -/
theorem innerCompiledVerifier_never_link (r : InnerCompilerInput) (never : ∀ x y τ, r.protocol.v.link.accept x y τ = false)
    (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (q : List Token × (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits)) :
    (innerCompiledVerifier r commitment prompt output q).evaluate hash = false := by
  have e : q = r.back (q.1, q.2.1.v, q.2.2.v) := rfl
  rw [e, ← verifyV_toInputV, verifyVDet_is]
  exact verifyVDet_never r.toInputV never hash _ _ _ _

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}

/-- **At the frame's letters.** -/
theorem innerCompiledVerifierAtFullSize_never (never : ∀ rr v, dec rr v = false)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (q : List Token × (KeyRoot 256 (innerCompilerInputAtFullSize T).protocol ×
      OfflineLinkOnlineProof 256 (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits (innerCompilerInputAtFullSize T).linkRoundSplits)) :
    (innerCompiledVerifier (innerCompilerInputAtFullSize T) commitment prompt output q).evaluate hash = false :=
  innerCompiledVerifier_never_link _
    (fun x y τ => linkW_never (ckP .two) ds frS.P.T.a xs dec never x y τ) hash _ _ _ q

end

end VerifiableInference.OnPublicFiles

#print axioms TypedOracleCompiler.Compile.Batch.verifyBS_never
#print axioms VerifiableInference.OnPublicFiles.verifyVDet_never
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_never_link
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierAtFullSize_never
