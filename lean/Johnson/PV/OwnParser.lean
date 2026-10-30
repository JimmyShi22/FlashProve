-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/OwnParser.lean: the hypothesis on the own parser's queries in the form of a bound of
fifteen.
`within_mono`, `fifteen_le_honestBudget`, `G8_describePolicyRef15`: G8 under the hypothesis that the
own parser asks at most fifteen queries.
That a parser of the prover's files meets this bound is not shown here.
A slot, no member: its letters are given no value here, and the description has run on no file. It
lays the coding of queries `mAll` (Johnson/PV/CutAll.lean), which is not the coding of the compiled
run. The full size alone. Conditional: no verifier that runs or ships is shown sound.

-/
import Johnson.PV.DescribePolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.K.Arm.ProofFront OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

/-- A parser within n is within every m ≥ n. -/
theorem within_mono {D : Description} {Z : PublicFiles} {Form : Type} (parse : Parser D Z Form) {n m : ℕ}
    (h : n ≤ m) (w : parse.Within n) : parse.Within m :=
  fun prompt output form => queryBound_mono_det _ _ _ h (w prompt output form)

theorem fifteen_le_honestBudget : 15 ≤ honestBudget := by
  unfold honestBudget
  norm_num

/-- **G8 AT THE REFERENCE SHAPE's NUMBERS, UNDER THE HYPOTHESIS THAT THE OWN PARSER ASKS AT MOST
FIFTEEN QUERIES.** -/
theorem G8_describePolicyRef15 (g : (Z : PublicFiles) → FramePol numsRef (ppAtFiles Z.pol Z.KL))
    (H : SideZ fun Z => (g Z).toFrame) (hA : BCHKS46At GF GE) (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (hk : ∀ Z, InScope Z = true → kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : ∀ Z, InScope Z = true → (g Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (g Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (g Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (g Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (hb : ∀ Z, InScope Z = true → ∀ x' a, (g Z).T₀.build x' a = Flat.buildReq x' a)
    (asks15 : ∀ Z, InScope Z = true → ∀ prompt output form,
      (H.parse Z prompt output form).toRandomized.QueryBound 15)
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      errDescribe (g Z).T₀ (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀).εs t n ≤ eps t n) :
    G8 fun _ => describeZ (fun Z => (g Z).toFrame) H :=
  G8_describePolicyRef g H hA eps ceil hk wK dK wP dP kS pS hb
    (fun Z _ h₁ _ => within_mono ((describeZ (fun Z => (g Z).toFrame) H).parse Z)
      fifteen_le_honestBudget (asks15 Z h₁))
    bound

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.within_mono
#print axioms VerifierAndGoals.Fit.G8_describePolicyRef15
