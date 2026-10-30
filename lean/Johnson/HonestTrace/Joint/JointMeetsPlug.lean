-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/JointMeetsPlug.lean

Nothing on hiding. No property of the protocol is claimed.
THE DEBT "serves" AT ANY FILLING OVER THE MATRICES WHOSE TRACE IS fullIn's READ THROUGH indexOf.
"serves_at_plug": such a filling's prover, where the maker returns, meets "AtPublicFiles.Committed.Serves": its test on the index
accepts every matrix in range, and it has a trace at what is written for every pair of the relation "RyesZ Z".
"servesAt_at_plug": so it meets "AtPublicFiles.AtFiles.ServesAt" at every Yes below "RyesZ Z": the type of the field "serves" of
"HonDebts" (E2E/RoadHonDebts.lean).
Limits: "made" (the maker returns) and the two equations on the filling are premises:
at the term's filling see JointMeets.lean.
"Serves" and "ServesAt" are two tests alone: they do not make "ready" return; nothing on cells, messages or acceptance.
The executable model's trace and the statements that tie it to the specification are not used: not imported.
-/
import Johnson.HonestTrace.Joint.JointMeetsIndex
import Johnson.HonestTrace.ReadyAtFullIn
import Johnson.FrontRoad.TracePremises
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Goal.Skeleton.SoundOfVerifyGoals
import E2E.BridgeJoinAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open OnBytes.HonestTrace
open ProofFile.Honest (OnlineProverParts OnlineProverWithDescription onlineProverFromPublicFiles fullIn)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open AtPublicFiles.Committed (RyesZ)
open VerifiableInference.OnPublicFiles.Flat (indexOf Holds)

section Plug
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {Rc X₀ X : Type}

/-- "Serves" at a prover over the matrices. The randomness's type Rc is a letter. -/
theorem serves_at_plug
    (scope : VerifierAndGoals.InScope Z = true) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {P : OnlineProverParts FullSizeMatrix Rc ProofFile.Honest.Cells X₀ X} {A : OnlineProverWithDescription FullSizeMatrix Rc ProofFile.Honest.Cells X₀ X}
    (hT : P.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ)
    (hR : P.inRange = fun M => (indexOf M).isSome)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    AtPublicFiles.Committed.Serves Z A.H := by
  obtain ⟨hZ, -⟩ := ProofFile.Honest.atPure_at_laid L made
  refine ⟨fun M hM => ?_, fun M x' rec hy => ?_⟩
  · obtain ⟨i, hi⟩ := hM
    rw [(ProofFile.Honest.atPure_ok made).2.2.2.2.2.1, hR]
    exact congrArg Option.isSome (VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl hi)
  · obtain ⟨pp, hr⟩ := VerifierAndGoals.AtTheName.read_of_scope Z scope
    obtain ⟨i, hi, hs⟩ := OnBytes.FrontRoad.served_of_valid Z Zp Np cF scope hr live L M x' hy
    have e : fullIn.trace Zp i (LPFD.Full.instanceAsPlainRecord (x', rec)) =
        some ⟨cellOf Zp.p.X (theTrace Zp.p.X i x'.val)⟩ :=
      fullIn_trace_of_servesAt hs x'.property rec
    rw [ProofFile.Honest.atPure_trace made, hT, hZ]
    show ((indexOf M).bind fun j => fullIn.trace Zp j (LPFD.Full.instanceAsPlainRecord (x', rec))).isSome = true
    rw [fullIn_trace_through_of_holds Zp hi, e]
    rfl

/-- The premise "ServesAt" of "honFit_atFiles" (E2E/BridgeJoinAtFiles.lean) at that prover, at the
committer's type of randomness and every Yes below "RyesZ Z". -/
theorem servesAt_at_plug
    (scope : VerifierAndGoals.InScope Z = true) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {P : OnlineProverParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Honest.Cells X₀ X} {A : OnlineProverWithDescription FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Honest.Cells X₀ X}
    (hT : P.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ)
    (hR : P.inRange = fun M => (indexOf M).isSome)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {Yes : FullSizeMatrix → LPFD.Full.XF → Prop} (hY : ∀ M x', Yes M x' → RyesZ Z M x') :
    AtPublicFiles.AtFiles.ServesAt Z A.H Yes := by
  exact AtPublicFiles.AtFiles.servesAt_of (Z := Z) (H := A.H) hY (serves_at_plug scope live L hT hR made)

end Plug

end HonestTraceRun.Meets

#print axioms HonestTraceRun.Meets.serves_at_plug
#print axioms HonestTraceRun.Meets.servesAt_at_plug
