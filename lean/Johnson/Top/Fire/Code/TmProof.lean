-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TmProof.lean: the three statements of TmStatement.lean, proved, at the full
size.

Why. What runs has a writing side with code; the soundness theorem's input has a bijective coding.
By their makers' word the two write the same strings at every oracle but the spare one. These
theorems say that the verifier cannot tell two such writing sides apart.
Main names. `noSpare : NoSpare`: the verifier `VRAV` never asks the spare oracle (the walk of
`asksIn_VRA`, Johnson/Top/InnerCompiledVerifierByPublicReading.lean, at the verifier's side). `tmAtVRAV : TmAtVRAV`: by
`noSpare` and `det_congr_asksIn`. `tmAtDvE : TmAtDvE …`: by `verifyVDet_is` (VerifyVDetProbe.lean)
at both inputs and `tmAtVRAV`.
Limits. The premise `SameOffSpare` is owed by whoever calls them: that a bijective coding exists
which agrees with the run's writing side off the spare oracle is not said here. Not enough for the
fast form at a family that is not `readBlocksV` of a writing side. AN EQUATION AT EACH HASH
FUNCTION: where a writing side names the hash (a run lays h₀ := Fmt.HO O; its digests are made at
the fixed hash) these theorems reach a member at each hash function, not one input bound outside the
probability. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.TmStatement
import Johnson.Top.Fire.Code.VerifyVDetProbe
import OnBytes.TypedOracleCompiler.Compile.Batch.NoOther
import OnBytes.TypedOracleCompiler.Run.PageRunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS SOf)
open Johnson.RunOne.StrictW (wqW assembleW stagesWL)

/-- The test of a seed asks the Fiat-Shamir oracle of the seeds' tag alone. -/
theorem asksIn_seedIsV {Y : Type} {lam : ℕ} {L : LHV Y} {Bd : Type} {aT : RoundSplits L.test.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (carrierV L Bd aT aL)) (S : SeedV lam W.K L Bd aT aL)
    (c : Dig lam) (s : L.Seed) :
    (seedIsV W S c s).AsksIn fun o _ => o ≠ TypedOracleCompiler.Compile.Batch.OracleName.other :=
  ⟨fun e => TypedOracleCompiler.Compile.Batch.OracleName.noConfusion e,
    fun _ => ⟨fun e => TypedOracleCompiler.Compile.Batch.OracleName.noConfusion e, fun _ => trivial⟩⟩

/-- **The verifier never asks the spare oracle.** -/
theorem noSpare : NoSpare := by
  intro Y lam L Bd aT aL W S cA r₀ p k x π
  unfold VRAV VCAV
  split
  · refine OComp.AsksIn.bind ?_ (asksIn_seedIsV W S _ _)
    intro _
    refine OComp.AsksIn.bind ?_ (asksIn_seedIsV W S _ _)
    intro _
    refine OComp.AsksIn.bind ?_
      (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _))
    intro _
    refine OComp.AsksIn.bind ?_
      (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _))
    intro _
    refine OComp.AsksIn.bind ?_
      (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _))
    intro _
    trivial
  · trivial

/-- **(Tm) at the verifier.** -/
theorem tmAtVRAV : TmAtVRAV := by
  intro Y lam L Bd aT aL W S cA r₀ p k x π m m' g h
  exact TypedOracleCompiler.Run.PageRun.det_congr_asksIn
    (P := fun o _ => o ≠ TypedOracleCompiler.Compile.Batch.OracleName.other) (fun o q ho => h o q ho)
    (noSpare Y lam L Bd aT aL W S cA r₀ p k x π)

variable {X : Type} (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
  (sT sB : Params.LinBindingShape) (early : X → X)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (K salt : ℕ)

local notation "LKe" => linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) ds frS.P.T.a xs dec
local notation "ALe" => _root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) ds)
local notation "LV" => LvOf DK DP runK runP rK rP sB.logLeaves early LKe
local notation "AT" => aTOf DK DP runK runP rK rP sB.logLeaves early LKe

/-- **(Tm) at the sheet's input.** -/
theorem tmAtDvE : TmAtDvE DK DP runK runP rK rP sT sB early ds xs dec K salt := by
  intro t cfg shape pl0 pl1 num seed r₀ p m m' enc build hash commitment prompt output proof h
  rw [verifyVDet_is, verifyVDet_is]
  unfold verifyVDet
  dsimp only [DvE, DvOf]
  cases build (prompt, output) proof.1 with
  | none => rfl
  | some x =>
    dsimp only
    cases enc proof.2.1 with
    | none => rfl
    | some code =>
      dsimp only
      by_cases hd : hash code = commitment
      · rw [if_pos hd, if_pos hd]
        exact tmAtVRAV X 256 LV (List Bool) AT ALe
          (probe_WV DK DP runK runP rK rP sB.logLeaves sT.logLeaves early LKe K salt ALe
            (wqW (ckP .two) ds frS.P.T.a xs dec K (chalP .two K))
            (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds)
            (TypedOracleCompiler.StringsList.prjT salt (ckP .two) ds))
          (probe_SdV DK DP runK runP rK rP sB.logLeaves early LKe (K + 1) ALe t cfg shape pl0 pl1
            num seed)
          (codeA (v := frS.P.v) (s := 1)) r₀ p proof.2.1 x proof.2.2 m m' (fun _ => hash) h
      · rw [if_neg hd, if_neg hd]

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.noSpare
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.tmAtVRAV
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.tmAtDvE
