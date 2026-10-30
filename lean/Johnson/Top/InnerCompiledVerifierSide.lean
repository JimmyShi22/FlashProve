-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InnerCompiledVerifierSide.lean: the verifier `innerCompiledVerifier r` of Johnson/Top/InnerCompiledVerifier.lean is, at
every input and every argument, the verifier written out over the verifier's side, `verifyV
r.toInputV` (Johnson/Top/InputV.lean).

Why. `innerCompiledVerifier r` is a field of an argument system made from the whole input: compiled, it would
need executable code for the decoder, the honest provers, the model and the honest committer.
`verifyV` reads thirteen things, none of them on the honest side. The theorems on soundness speak of
`innerCompiledVerifier`. This file says that the two are one function.
Main names (namespace `VerifiableInference.OnPublicFiles`):
  `InnerCompilerInput.toInputV r`: the thirteen things that the verifier's own body reads; thirteen equations
    by rfl tie its fields to r's.
  `innerCompiledVerifier_written`: `innerCompiledVerifier r` with the layers of the argument system unfolded: `verifyBuilt`
    over `verifyDigestKey` over `verifyAtKeyRoot` carried over the one hash function.
  `innerCompiledVerifier_eq`: `innerCompiledVerifier r c p o pf = verifyV r.toInputV c p o (pf.1, pf.2.1.v, pf.2.2.v)`: no
    hypothesis; every argument is bound. Its proof rests on four ties: `Arg.buildInstance_V`
    (ZKCP/BuildInstanceSide.lean), `OComp.overOne_v` (Rom/FamilySide.lean), `VRA_v`
    (Johnson/TypedOracleCompiler/RecCompile/FrontRootAnsSide.lean) and, through it, `VCA_v` (CmsAnsSide.lean,
    there). The other ties of the files named ...Side.lean say the same layer by layer.
Limits: an equation of two algorithms with an oracle; so they agree at every hash function. The
goals' `verify` (Ladder.lean) calls `innerCompiledVerifier`; nothing here names it. That a concrete `InputV` is
`r.toInputV` for some r, or has executable code, is not said. Nothing on soundness.

-/
import Johnson.Top.InnerCompiledVerifier
import Johnson.Top.InputV

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable (r : InnerCompilerInput)

/-- The verifier's side of the input. -/
def InnerCompilerInput.toInputV : InputV :=
  ⟨r.Instance, r.protocol.v, r.LeafBody, r.offlineRoundSplits, r.linkRoundSplits, r.queryLayout, r.seedQueries.v, r.answerCode, r.fixedSample, r.compilerParameters, r.oracleCoding.v,
    fun k => r.keyCode ⟨k.cm, k.rcd⟩, r.buildInstance⟩

/-! The thirteen fields of the verifier's side are the input's own; four of them (protocol, seedQueries, oracleCoding, keyCode) are
read at the verifier's side, and keyCode's equation is stated for each key. These equations type-check
only while the texts of `InputV` and `InnerCompilerInput` agree. -/

theorem InnerCompilerInput.toInputV_X : r.toInputV.X = r.Instance := rfl
theorem InnerCompilerInput.toInputV_L : r.toInputV.L = r.protocol.v := rfl
theorem InnerCompilerInput.toInputV_Bd : r.toInputV.Bd = r.LeafBody := rfl
theorem InnerCompilerInput.toInputV_aT : r.toInputV.aT = r.offlineRoundSplits := rfl
theorem InnerCompilerInput.toInputV_aL : r.toInputV.aL = r.linkRoundSplits := rfl
theorem InnerCompilerInput.toInputV_W : r.toInputV.W = r.queryLayout := rfl
theorem InnerCompilerInput.toInputV_Sd : r.toInputV.Sd = r.seedQueries.v := rfl
theorem InnerCompilerInput.toInputV_cA : r.toInputV.cA = r.answerCode := rfl
theorem InnerCompilerInput.toInputV_r₀ : r.toInputV.r₀ = r.fixedSample := rfl
theorem InnerCompilerInput.toInputV_p : r.toInputV.p = r.compilerParameters := rfl
theorem InnerCompilerInput.toInputV_m : r.toInputV.m = r.oracleCoding.v := rfl
theorem InnerCompilerInput.toInputV_enc (k : KeyRoot 256 r.protocol) : r.toInputV.enc k.v = r.keyCode k := rfl
theorem InnerCompilerInput.toInputV_build : r.toInputV.build = r.buildInstance := rfl

/-- The verifier with the layers of the argument system unfolded. -/
theorem innerCompiledVerifier_written (commitment : Commitment) (prompt output : List Token)
    (proof : (innerSystem r).Proof) :
    innerCompiledVerifier r commitment prompt output proof =
      deterministicOf (ZKCP.verifyBuilt (ZKCP.verifyDigestKey
        (fun k x π => Rom.ofRom ((verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters k x π).overOne r.oracleCoding)) r.keyCode) r.buildInstance
        commitment (prompt, output) proof) := by
  show deterministicOf ((((Rec.digestKeyScheme (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r)) r.keyCode).coinsFirst
    r.coinBound).buildInstance r.buildInstance (fun _ => []) r.fallbackProof).V commitment (prompt, output) proof) = _
  rw [ZKCP.Arg.buildInstance_V]
  rfl

/-- **The verifier of the argument system is the verifier written out**, at every input, commitment,
prompt, output and proof. -/
theorem innerCompiledVerifier_eq (commitment : Commitment) (prompt output : List Token)
    (proof : (innerSystem r).Proof) :
    innerCompiledVerifier r commitment prompt output proof =
      verifyV r.toInputV commitment prompt output (proof.1, proof.2.1.v, proof.2.2.v) := by
  have h : (fun (k : KeyRoot 256 r.protocol) (x : r.Instance) (π : OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) =>
      Rom.ofRom ((verifyAtKeyRoot r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters k x π).overOne r.oracleCoding)) =
      fun k x π => Rom.ofRom
        ((VRAV (L := r.protocol.v) r.queryLayout r.seedQueries.v r.answerCode r.fixedSample r.compilerParameters k.v x π.v).overOneV r.oracleCoding.v) := by
    funext k x π
    rw [OComp.overOne_v, VRA_v]
  rw [innerCompiledVerifier_written, h]
  rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_written
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_eq
