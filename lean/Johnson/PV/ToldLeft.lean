-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/ToldLeft.lean: what is owed at the value `toldOf U` (Johnson/PV/ToldMember.lean): of the
  sixteen named hypotheses at every d, thirteen are shown here, at every d. CONDITIONAL: left are
  keySound, proofSound and the meaning.

Twelve by the terms of `compilerSoundnessConditionsWithFixedLinkAtFullSize` (Johnson/Flat/TwoSizesAt.lean), which read no d (seedLaw by
  `outOfDomainSampleQueryLayoutOfCode_law`, which is general in the five letters that are laid from d), and the commitment by
  `told_code`.
Under: the theorem on codes (hA); five tests on numbers (hk, wK, dK, wP, dP); keySound and
  proofSound (at the frame's own names: they read no d); the meaning (hs); and, riding in U: two
  tests on the data (`kindsAndWorkBelow256`), K + 2 < 2 ^ 49, the front set's three laws; in T₀: hSeed, hε. The
  relation, the instance and the bound on a round's error are those of `soundnessAnalysisDataWithFixedLinkAtFullSize T₀`.
Limits: it is still no member of the statement's premises: keySound, proofSound and the meaning are
  shown at no letters.

-/
import Johnson.PV.ToldSound
import Johnson.PV.ToldThin

set_option autoImplicit false
set_option maxRecDepth 40000

noncomputable section
open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.K.Arm.ProofFront OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ} {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early
      salt).Provers}
  {T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P} (U : ToldLetters T₀)

/-- **THE FIFTEEN AT EVERY d, FROM keySound AND proofSound.** -/
theorem core_toldOf (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀)) (d : (toldOf U).D) :
    CompilerSoundnessConditions ((toldOf U).beside (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).Wn (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).Rno (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).x₀
                          (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).εs d) :=
  (toldOf U).core_from (soundnessAnalysisDataWithFixedLinkAtFullSize T₀) (told_code U) ((threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK
                                    runP rK rP depthReq early salt).obj_noneColl P) kS
    (entrySoundWithFixedLinkAtFullSize hA T₀) pS (threeProtocolsWithFixedLinkAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq
                      early salt).1 (threeProtocolsWithFixedLinkAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early
                      salt).2.1
    (threeProtocolsWithFixedLinkAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2.2
        (threeProtocolsWithFixedLinkAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).1
        (threeProtocolsWithFixedLinkAtFullSize_entryCoherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt)
    (threeProtocolsWithFixedLinkAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2 (wiresOfFull A
                                                        (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P K T₀.depthReqT hk wK dK wP dP)
    (fun _ => outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y =>
      le_trans (entryFull_seedLawK A (relationsAndEncodingOfClaims A E) T₀.W.K T₀.hK y) T₀.hε)
    (fun _ => codeA_inj) (fun _ => codeA_one) d

/-- **THE TOLD LAW AT THE VALUE, FROM WHAT IS OWED THERE**: keySound, proofSound, the meaning; under
the theorem on codes and five tests on numbers. Riding in U: two tests on the data, K + 2 < 2^49,
the front set's three
laws; in T₀: hSeed, hε. -/
theorem sound_toldOf_left (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀)) (hs : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀))
    (d₀ : (toldOf U).D) :
    Sound (toldOf U).system fun t =>
      soundnessBoundOverTypedOracles (innerCompilerInputWithFixedLinkAtFullSize T₀).queryLayout (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).εs t 0 + epsCode t :=
  sound_toldOf U d₀ _ _ _ _ fun d =>
    ⟨core_toldOf U hA hk wK dK wP dP kS pS d, (toldOf U).sound_from (soundnessAnalysisDataWithFixedLinkAtFullSize T₀) hs d⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.core_toldOf
#print axioms VerifiableInference.OnPublicFiles.sound_toldOf_left
