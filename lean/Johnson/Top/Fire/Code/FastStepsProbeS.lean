-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Top.Fire.Code.VerifyVFastStepsDS

/-! The statement `FastStepsIs`, proved: so it is not false.-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutDS
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS SOf)
open Johnson.RunOne.StrictW (wqW assembleW stagesWL)

variable {X : Type} (DK DP : WholeD) (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecSmall)
  (sT sB : Params.LinBindingShape) (early : X → X)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecSmall × RecSmall → PQ.View → Bool) (K salt : ℕ)

theorem fastSteps_is : FastStepsIs DK DP runK runP rK rP sT sB early ds xs dec K salt := by
  intro t cfg shape pl0 pl1 num seed r₀ p F enc build hash commitment prompt output aux cm rcd
    copy fT e fB
  unfold fastF fastSteps
  cases build (prompt, output) aux with
  | none => rfl
  | some x =>
    dsimp only
    cases enc ⟨cm, rcd⟩ with
    | none => rfl
    | some code =>
      dsimp only
      by_cases hd : hash code = commitment
      · rw [if_pos hd, if_pos hd]
        cases piTE DK DP runK runP rK rP sT sB early ds xs dec fT with
        | none =>
          cases piLE DK DP runK runP rK rP sB early ds xs dec e <;>
            cases piBE DK DP runK runP rK rP sB early ds xs dec fB <;> rfl
        | some πT =>
          cases piLE DK DP runK runP rK rP sB early ds xs dec e with
          | none => cases piBE DK DP runK runP rK rP sB early ds xs dec fB <;> rfl
          | some πL =>
            cases piBE DK DP runK runP rK rP sB early ds xs dec fB with
            | none => rfl
            | some πB => rfl
      · rw [if_neg hd, if_neg hd]
        rfl

end VerifiableInference.OnPublicFiles.SlotsBehindCutDS

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.fastSteps_is
