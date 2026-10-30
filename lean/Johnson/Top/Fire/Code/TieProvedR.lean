-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TieProvedR.lean: THE PROPOSITION OF TieStatedR.lean, PROVED, and what of the
tie's premises is met at every T. The full size.
  `tieT2R` : `TieT2R` at all the section's letters. How: `fastF_reads_is_verifyV`
  (FastFamProbe.lean) at mR; `tmAtDvE` (TmProof.lean) from mR to T.m.v;
    `tie_verify` (TieProved.lean).
  `tie_rest_meets`: AT EVERY T the premises of `TieT1`, `TieT2D`, `TieT2F` beside T can be met
  together: there is a shape sT of the asked depth, and at every O
    a family that meets `ReadsAs T.m.v O` (what T.m.v itself reads). So these statements are empty
    only where no T is.
  `tie_restR_meets`: the like for `TieT2R`, at mR := T.m.v.
LIMITS: those of TieStatedR.lean's head. `tie_rest_meets` lays no T, and its family is not one that
a run calls.

-/
import Johnson.Top.Fire.Code.TieStatedR
import Johnson.Top.Fire.Code.TieProved
import Johnson.Top.Fire.Code.TmProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (SOf)

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull)
  (sB : Params.LinBindingShape) (early : X → X) (salt K : ℕ)
  (P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt).Provers)

set_option maxRecDepth 20000 in
/-- **(T2), for what runs, through the link at the spare oracle.** -/
theorem tieT2R : TieT2R A E DK DP runK runP ds xs dec rK rP sB early salt K P :=
  fun T sT h O mR Ff hR hS commitment prompt output aux cm rcd copy fT e fB =>
  (fastF_reads_is_verifyV DK DP runK runP rK rP sT sB early ds xs dec K salt
      T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p mR
      (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build O Ff hR commitment prompt output aux cm rcd copy fT e fB).trans
    ((tmAtDvE DK DP runK runP rK rP sT sB early ds xs dec K salt
      T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p mR T.m.v
      (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build (hashOf O) commitment prompt output
      (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB) hS).trans
    (congrArg (fun a : DeterministicAlgorithm Bool => a.evaluate (hashOf O))
      (tie_verify T sT h commitment prompt output aux cm rcd copy fT e fB)))

variable {A E DK DP runK runP ds xs dec rK rP sB early salt K P}

/-- **At every T the premises beside T can be met together.** -/
theorem tie_rest_meets (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) :
    ∃ sT : Params.LinBindingShape, sT.logLeaves = T.depthReqT ∧
      ∀ O : ByteArray → ByteArray,
        ∃ Ff : Fam (typedOracleFamily 256 (K + 1) (carrierV (DvET T sT).L (List Bool) (DvET T sT).aT (DvET T sT).aL)),
          ReadsAs T.m.v O Ff :=
  ⟨⟨T.depthReqT, 0⟩, rfl, fun O =>
    ⟨fun o q => (T.m.v.rng o).symm fun j => TypedOracleCompiler.Run.PageRun.gOf O () (T.m.v.code o q j), fun _ _ => rfl⟩⟩

/-- The like for `TieT2R`, at mR := T.m.v. -/
theorem tie_restR_meets (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) :
    ∃ sT : Params.LinBindingShape, sT.logLeaves = T.depthReqT ∧
      ∀ O : ByteArray → ByteArray,
        ∃ (mR : ImplV (typedOracleFamily 256 (K + 1) (carrierV (DvET T sT).L (List Bool) (DvET T sT).aT (DvET T sT).aL)) 256)
          (Ff : Fam (typedOracleFamily 256 (K + 1) (carrierV (DvET T sT).L (List Bool) (DvET T sT).aT (DvET T sT).aL))),
          ReadsAs mR O Ff ∧ SameOffSpare mR T.m.v (fun _ => hashOf O) :=
  ⟨⟨T.depthReqT, 0⟩, rfl, fun O =>
    ⟨T.m.v, fun o q => (T.m.v.rng o).symm fun j => TypedOracleCompiler.Run.PageRun.gOf O () (T.m.v.code o q j),
      fun _ _ => rfl, fun _ _ _ => rfl⟩⟩

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.tieT2R
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.tie_rest_meets
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.tie_restR_meets
