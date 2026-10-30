-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/DescribePolicy.lean: the goals G8 and G7 at a family of frames whose claims are made of
what the reader of the public files returned (scales and policy).
`FramePol`: the letters at one Z. `G8_describePolicy`, `G7_describePolicy`: `meaning` and `carries`
are no hypotheses any more: they are taken from Johnson/Flat/PolicyAtFrame.lean.
`G8_describePolicyRef`: at the reference shape's numbers the two bounds on the matrix's shape are
`numsRef_fits`.
The meaning has moved, not shrunk: proofSound must give the relation at the files' own table and
policy.
A slot, no member: its letters are given no value here, and the description has run on no file. It
lays the coding of queries `mAll` (Johnson/PV/CutAll.lean), which is not the coding of the compiled
run. The full size alone. Conditional: no verifier that runs or ships is shown sound.

-/
import Johnson.PV.DescribeZ
import Johnson.Flat.PolicyAtFrame
import Johnson.Flat.ThreeFull

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
open Inst.Model.Layout (kRef hRef)
open scoped ENNReal

/-- The letters at one Z, at requests and at what the reader returned (scales and policy). -/
structure FramePol (N : MatrixNums) (pp : Inst.Model.ScalesAndPolicy) where
  E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)
  DK : WholeD
  DP : WholeD
  runK : RecFull → PQ.View → PQ.View → PQ.View → Bool
  runP : Flat.Req × RecFull → PQ.View → PQ.View → PQ.View → Bool
  rK : RecFull
  rP : RecFull
  depthReq : ℕ
  early : Flat.Req → Flat.Req
  salt : ℕ
  K : ℕ
  P : (threeProtocolsWithFixedLinkAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) (relationsAndEncodingOfClaims _ E) DK DP runK runP rK rP
    depthReq early salt).Provers
  T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DK DP runK runP rK rP
    depthReq early salt K P
  U : ToldLetters T₀

/-- As a frame; φ is `phiAt`. -/
def FramePol.toFrame {N : MatrixNums} {pp : Inst.Model.ScalesAndPolicy} (g : FramePol N pp) : FrameAt where
  X := Flat.Req
  A := claimsReqAt (frS.toDecR frZ 402653181) N pp
  E := g.E
  DK := g.DK
  DP := g.DP
  runK := g.runK
  runP := g.runP
  rK := g.rK
  rP := g.rP
  depthReq := g.depthReq
  early := g.early
  salt := g.salt
  K := g.K
  P := g.P
  T₀ := g.T₀
  U := g.U
  φ := fun _ valid => phiAt valid

variable (N : MatrixNums) (g : (Z : PublicFiles) → FramePol N (ppAtFiles Z.pol Z.KL))
  (H : SideZ fun Z => (g Z).toFrame)

/-- **THE GOAL G8, «meaning» AND «carries» PAID.** -/
theorem G8_describePolicy (hA : BCHKS46At GF GE) (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (hk : ∀ Z, InScope Z = true → kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : ∀ Z, InScope Z = true → (g Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (g Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (g Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (g Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (hrows : N.rows ≤ hRef) (hcols : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (hb : ∀ Z, InScope Z = true → ∀ x' a, (g Z).T₀.build x' a = Flat.buildReq x' a)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((describeZ (fun Z => (g Z).toFrame) H).parse Z) honestBudget)
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      errDescribe (g Z).T₀ (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀).εs t n ≤ eps t n) :
    G8 fun _ => describeZ (fun Z => (g Z).toFrame) H :=
  G8_describeZ_left (fun Z => (g Z).toFrame) H hA eps ceil hk wK dK wP dP kS pS
    (fun Z => claimPolicy (ppAtFiles Z.pol Z.KL) (lawful_ppAtFiles Z.pol Z.KL))
    (fun Z h₁ => meaningPolicyOfFull N (ppAtFiles Z.pol Z.KL) (g Z).E (g Z).DK (g Z).DP (g Z).runK
      (g Z).runP (g Z).rK (g Z).rP (g Z).depthReq (g Z).early (g Z).salt (g Z).K (g Z).P
      (lawful_ppAtFiles Z.pol Z.KL) hrows hcols (g Z).T₀ (hb Z h₁))
    (fun _ _ _ hr i prompt output h =>
      carriesPolicy (ppAtFiles_of_read hr) _ (valid_of_read hr) i prompt output h)
    ownParser bound

/-- **THE GOAL G7 THERE, FROM THE SAME DEBTS.** -/
theorem G7_describePolicy (hA : BCHKS46At GF GE) (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (hk : ∀ Z, InScope Z = true → kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : ∀ Z, InScope Z = true → (g Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (g Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (g Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (g Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀))
    (hrows : N.rows ≤ hRef) (hcols : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (hb : ∀ Z, InScope Z = true → ∀ x' a, (g Z).T₀.build x' a = Flat.buildReq x' a)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((describeZ (fun Z => (g Z).toFrame) H).parse Z) honestBudget)
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      errDescribe (g Z).T₀ (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀).εs t n ≤ eps t n) :
    G7 fun _ => describeZ (fun Z => (g Z).toFrame) H :=
  g7_of_g8 _ (G8_describePolicy N g H hA eps ceil hk wK dK wP dP kS pS hrows hcols hb ownParser
      bound)

/-- **THE GOAL G8 AT THE REFERENCE SHAPE's NUMBERS**: N := numsRef: the two bounds on the matrix's
shape are paid by `numsRef_fits` (Johnson/Flat/ThreeFull.lean:117). -/
theorem G8_describePolicyRef (g : (Z : PublicFiles) → FramePol numsRef (ppAtFiles Z.pol Z.KL))
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
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((describeZ (fun Z => (g Z).toFrame) H).parse Z) honestBudget)
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      errDescribe (g Z).T₀ (soundnessAnalysisDataWithFixedLinkAtFullSize (g Z).T₀).εs t n ≤ eps t n) :
    G8 fun _ => describeZ (fun Z => (g Z).toFrame) H :=
  G8_describePolicy numsRef g H hA eps ceil hk wK dK wP dP kS pS numsRef_fits.1 numsRef_fits.2 hb
    ownParser bound

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.G8_describePolicyRef
#print axioms VerifierAndGoals.Fit.G8_describePolicy
#print axioms VerifierAndGoals.Fit.G7_describePolicy
