-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/CoreOfFit.lean: at the full-size frame with the entry file's three letters: the fifteen
named hypotheses of `CompilerSoundnessConditions` (Johnson/Top/InnerCompiledVerifier.lean) FROM THE ONE TEST ON NUMBERS
(`sizeNumbersFitAtFullSize`, Johnson/Flat/Dec/FailsClosed.lean) and the four that are left; and these four with the three on
soundness asked ONLY WHERE A LETTER live SAYS YES, if where it says no the three decisions never say yes.

  `compilerSoundnessConditionsAtFullSize_of_fit`: one call of `compilerSoundnessConditionsAtFullSize` (Johnson/Flat/Dec/TwoSizesAt.lean): its nine premises on numbers are
    read off the test's yes.
  `remainingSoundnessConditionsAtFullSize_live`: `RemainingSoundnessConditionsAtFullSize T` from: commitment; live : Bool; the three decisions never say yes where live is
    false; keySound, entrySound, proofSound where live is true.
Limits: conditionals. WHERE live IS FALSE THE THREE HOLD FOR NOTHING (a verifier that refuses all). Nothing is shown of any decision. NO VALUE OF
THIS FRAME HAS RUN ON A REAL PROOF. The full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.FailsClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  {T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P}

/-- **The fifteen, from the one test on numbers and the four that are left.** -/
theorem compilerSoundnessConditionsAtFullSize_of_fit {v : ℕ}
    (hfit : sizeNumbersFitAtFullSize K v depthReq T.depthReqT DK DP ds xs = true) (h : RemainingSoundnessConditionsAtFullSize T) :
    CompilerSoundnessConditions (soundnessAnalysisDataAtFullSize T) :=
  have f := frameFitFullD_parts hfit
  compilerSoundnessConditionsAtFullSize f.hk f.hE.bL f.hE.wLk f.hE.own f.hE.dL f.wK f.dK f.wP f.dP h

/-- **The four that are left, the three on soundness asked only where live says yes.** -/
theorem remainingSoundnessConditionsAtFullSize_live (live : Bool)
    (deadK : live = false → ∀ r v₁ v₂ v₃, runK r v₁ v₂ v₃ = false)
    (deadE : live = false → ∀ rr v, dec rr v = false)
    (deadP : live = false → ∀ x v₁ v₂ v₃, runP x v₁ v₂ v₃ = false)
    (kS : live = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T))
    (eS : live = true → CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T))
    (pS : live = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T))
    (cm : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataAtFullSize T)) : RemainingSoundnessConditionsAtFullSize T := by
  cases live with
  | false =>
    exact ⟨keySoundOfFullD_of_never (deadK rfl) T, entrySoundOfFullD_of_never (deadE rfl) T,
      proofSoundOfFullD_of_never (deadP rfl) T, cm⟩
  | true => exact ⟨kS rfl, eS rfl, pS rfl, cm⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.compilerSoundnessConditionsAtFullSize_of_fit
#print axioms VerifiableInference.OnPublicFiles.remainingSoundnessConditionsAtFullSize_live
