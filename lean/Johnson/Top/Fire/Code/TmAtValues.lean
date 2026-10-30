-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TmAtValues.lean (the request's item is a letter `it`: Dec/MOneD.lean's head says why): the one premise of (Tm) (TmStatement.lean, `SameOffSpare`) is
met at the full size's values (Johnson/PV/MFullOne.lean, in its twin with the entry's decision a letter: Dec/MOneD.lean): the writing side that
is laid for a run (`mFLaidD`) and the writing side of the coding that is one to one and onto by its
type (`mFOneD`).

Why. A theorem with a premise says nothing where the premise cannot be met. Here it is met, at the
two records for which (Tm) was stated.
Main names. `sameOffSpare_mFD`: at every hash function. `tmAtLaidFD`: so the evaluation of `verifyV` at
`DvE` with `mFLaidD` is its evaluation at `DvE` with `mFOneD`'s writing side: at every commitment,
prompt, output and proof.
Under. `mFOneD`'s own three conditions, all on data: `kindsAndWorkBelow256` of both files' data; K + 2 < 2 ^ 49; the
configuration's digest has 32 bytes.
Limits. `mF_codeD` carries the load. At FREE letters in `mFLaidD`'s form: that a
run's own letters have that form is Vals/LaidAtRun.lean's (a file that is not part of this tree).
THE CODING THAT IS REACHED NAMES THE HASH
where h₀ does (a run lays h₀ := Fmt.HO O; c, pdL, dK, dP are made at the fixed hash): a member at
each hash function, not one input bound outside the probability. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.TmProof
import Johnson.Top.Fire.Code.Dec.MOneD

set_option autoImplicit false
set_option maxRecDepth 40000

namespace PV.MFull
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run TypedOracleCompiler.Run.SerArm OnBytes.K.Arm.Pub OnBytes.Tie TypedOracleCompiler.Slice VerifiableInference.OnPublicFiles
open OnBytes.K.Arm
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

open PV.OkOwn (okOwnF)
open VerifiableInference

variable (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : (ReqAt Inst.Model.ppref) × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull)
  (early : (ReqAt Inst.Model.ppref) → (ReqAt Inst.Model.ppref)) (salt : ℕ) (K : ℕ)
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains) (it : ReqAt Inst.Model.ppref → ByteArray) (r₀ : RecFull)
  (c : ByteArray) (hc : c.size = 32) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
  (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : K + 1 + 1 < 2 ^ 49)

/-- **The premise of (Tm) is met** at the value that is laid and the bijective coding's writing side. -/
theorem sameOffSpare_mFD (depthReq : ℕ) (g : Fam (rom 256)) :
    SameOffSpare (mFLaidD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP)
      (mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP hK).v g := by
  intro o q ho
  exact congrArg ((mFLaidD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP).rng o).symm
    (funext fun j => congrArg (g ())
      (mF_codeD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP hK o ho q j))

/-- **(Tm) at these two.** -/
theorem tmAtLaidFD (sT sB : OnBytes.Params.LinBindingShape) :
    ∀ t cfg shape pl0 pl1 num seed r₁ p enc build hash commitment prompt output proof,
    (verifyV
        (DvE DK DP runK runP rK rP sT sB early PV.EntryFive.dsF PV.EntryFive.xsF dec
          K salt t cfg shape pl0 pl1 num seed r₁ p
          (mFLaidD DK DP runK runP dec rK rP sB.logLeaves early salt K h₀ k c' it r₀ c hc sR pdL dK dP) enc build)
        commitment prompt output proof).evaluate hash =
      (verifyV
        (DvE DK DP runK runP rK rP sT sB early PV.EntryFive.dsF PV.EntryFive.xsF dec
          K salt t cfg shape pl0 pl1 num seed r₁ p
          (mFOneD DK DP runK runP dec rK rP sB.logLeaves early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP hK).v enc build)
        commitment prompt output proof).evaluate hash := by
  intro t cfg shape pl0 pl1 num seed r₁ p enc build hash commitment prompt output proof
  exact tmAtDvE DK DP runK runP rK rP sT sB early PV.EntryFive.dsF PV.EntryFive.xsF
    dec K salt t cfg shape pl0 pl1 num seed r₁ p _ _ enc build hash commitment prompt
    output proof
    (sameOffSpare_mFD DK DP runK runP dec rK rP early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP
      hK sB.logLeaves fun _ => hash)

end PV.MFull

#print axioms PV.MFull.sameOffSpare_mFD
#print axioms PV.MFull.tmAtLaidFD
