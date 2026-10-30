-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/DescribeLeft.lean: the goals at `describeFull V` from the hypotheses that are left at the
full size.
`core_describe`: the told law's core at every Z and every d from keySound, proofSound, the theorem
on codes (a hypothesis here) and five tests on numbers (`core_toldOf`, Johnson/PV/ToldLeft.lean).
`G7_describe_left`, `G8_describe_left`: the goals from these, `meaning` and `carries`.
A slot, no member: its letters are given no value here, and the description has run on no file. It
lays the coding of queries `mAll` (Johnson/PV/CutAll.lean), which is not the coding of the compiled
run. The full size alone. Conditional: no verifier that runs or ships is shown sound.

-/
import Johnson.PV.Describe
import Johnson.PV.ToldLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.K.Arm.ProofFront OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}
  {T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P}
  (V : DescribeLetters T₀)

/-- **core at describeFull V, at every Z and every d, from keySound and proofSound.** -/
theorem core_describe (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀)) (Z : PublicFiles) (d : (toldAtZ V Z).D) :
    CompilerSoundnessConditions ((toldAtZ V Z).beside (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).Wn (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).Rno
                          (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).x₀ (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).εs d) :=
  core_toldOf (atZ V.U Z) hA hk wK dK wP dP kS pS d

/-- **THE GOAL G7 AT describeFull V**, from the hypotheses that the head names. -/
theorem G7_describe_left (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀))
    (claim : A.Mat → List Token → List Token → Prop)
    (meaning : ∀ i (x' : List Token × List Token) a x, T₀.build x' a = some x →
      (∃ w, (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).Rno i x w) → claim i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      pp.pol = Inst.Model.AcceptancePolicy.exact → ∀ i prompt output, claim i prompt output →
        ModelOutput (settingsOfRead pp) (V.φ (settingsOfRead pp) (valid_of_read hr) i) prompt
            output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      pp.pol = Inst.Model.AcceptancePolicy.exact → Parser.Within ((describeFull V).parse Z) honestBudget)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget →
      errDescribe T₀ (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).εs t n ≤ ceiling) :
    G7 fun _ => describeFull V :=
  G7_describe V claim _ _ _ _ (fun Z _ d => core_describe V hA hk wK dK wP dP kS pS Z d) meaning
    carries ownParser ceil

/-- **THE GOAL G8 AT describeFull V**, likewise. -/
theorem G8_describe_left (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀))
    (claim : A.Mat → List Token → List Token → Prop)
    (meaning : ∀ i (x' : List Token × List Token) a x, T₀.build x' a = some x →
      (∃ w, (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).Rno i x w) → claim i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      ∀ i prompt output, claim i prompt output →
        Policy.MeetsPolicy (settingsOfRead pp) pp.pol (V.φ (settingsOfRead pp) (valid_of_read hr) i)
          prompt output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((describeFull V).parse Z) honestBudget)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget →
      errDescribe T₀ (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).εs t n ≤ ceiling) :
    G8 fun _ => describeFull V :=
  G8_describe V claim _ _ _ _ (fun Z _ d => core_describe V hA hk wK dK wP dP kS pS Z d) meaning
    carries ownParser ceil

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.core_describe
#print axioms VerifierAndGoals.Fit.G7_describe_left
#print axioms VerifierAndGoals.Fit.G8_describe_left
