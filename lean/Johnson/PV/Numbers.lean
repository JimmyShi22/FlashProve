-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/Numbers.lean: the hypotheses on the error's bound and its ceiling as tests on numbers.
`G8_describeNumbers`, `G7_describeNumbers`: the error is `epsFrame s v`
(Johnson/Flat/CountAtFrame.lean), under a + s = 128, s <= 55, c <= 5/4, v <= 2^63, a stated round
error of at most c * 2^-a and a count of the compiled verifier's queries of at most v.
Two limits: beyond the range of the level function of that file the bound is infinite; the ceiling
costs three bits, so the stated round error must lie between 2^-128 and (5/4) * 2^-73.
A slot, no member: its letters are given no value here, and the description has run on no file. It
lays the coding of queries `mAll` (Johnson/PV/CutAll.lean), which is not the coding of the compiled
run. The full size alone. Conditional: no verifier that runs or ships is shown sound.

-/
import Johnson.PV.OwnParser
import Johnson.Flat.CountAtFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

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

/-- **THE GOAL G8, «bound» AND «ceil» PAID BY NUMBERS.** -/
theorem G8_describeNumbers (g : (Z : PublicFiles) → FramePol numsRef (ppAtFiles Z.pol Z.KL))
    (H : SideZ fun Z => (g Z).toFrame) (hA : BCHKS46At GF GE)
    (c : ℝ≥0∞) (a s v : ℕ) (has : a + s = 128) (hs : s ≤ 55) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (hv : v ≤ 2 ^ 63)
    (he : ∀ Z, InScope Z = true → (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀).εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹)
    (hcnt : ∀ Z, InScope Z = true →
      cntFrameFull (g Z).DK (g Z).DP (g Z).depthReq (g Z).T₀.depthReqT ≤ v)
    (hk : ∀ Z, InScope Z = true → kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : ∀ Z, InScope Z = true → (g Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (g Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (g Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (g Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (hb : ∀ Z, InScope Z = true → ∀ x' a, (g Z).T₀.build x' a = Flat.buildReq x' a)
    (asks15 : ∀ Z, InScope Z = true → ∀ prompt output form,
      (H.parse Z prompt output form).toRandomized.QueryBound 15) :
    G8 fun _ => describeZ (fun Z => (g Z).toFrame) H :=
  G8_describePolicyRef15 g H hA (epsFrame s v)
    (fun t n ht hn => ceil_of_numbers s v hs hv t n ht hn) hk wK dK wP dP kS pS hb asks15
    (fun Z h t n => bound_of_numbers (g Z).T₀.W _ c a s v has (he Z h) hc
      (le_of_eq_of_le (tVC_wireOfFull _ _ _ _ _ _ _ _ _ _ _ _ _ _) (hcnt Z h)) t n)

/-- **THE GOAL G7 THERE**, from the same. -/
theorem G7_describeNumbers (g : (Z : PublicFiles) → FramePol numsRef (ppAtFiles Z.pol Z.KL))
    (H : SideZ fun Z => (g Z).toFrame) (h : G8 fun _ => describeZ (fun Z => (g Z).toFrame) H) :
    G7 fun _ => describeZ (fun Z => (g Z).toFrame) H := g7_of_g8 _ h

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.G8_describeNumbers
#print axioms VerifierAndGoals.Fit.G7_describeNumbers
