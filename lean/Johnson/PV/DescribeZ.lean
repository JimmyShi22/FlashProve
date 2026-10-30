-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/DescribeZ.lean: the description of Johnson/PV/Describe.lean with letters that are
functions of the public files.
`FrameAt`: the letters at one Z. `SideZ`: the honest side, the form and the parser. `describeZ fr
H`: the value; `input_describeZ`: its input at Z is `describeFull`'s at that Z's frame.
`G7_describeZ_left`, `G8_describeZ_left`: the goals, every hypothesis asked at every Z in scope at
that Z's frame, one bound on the error over all. `G7_describeZ_by_G8`: G7 from G8's hypotheses
alone, by `g7_of_g8`.
A slot, no member: its letters are given no value here, and the description has run on no file. It
lays the coding of queries `mAll` (Johnson/PV/CutAll.lean), which is not the coding of the compiled
run. The full size alone. Conditional: no verifier that runs or ships is shown sound.

-/
import Johnson.PV.DescribeLeft

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

/-- All the letters of Describe.lean at one Z. -/
structure FrameAt where
  X : Type
  A : (frS.toDecR frZ 402653181).Claims X
  E : Coding A
  DK : WholeD
  DP : WholeD
  runK : RecFull → PQ.View → PQ.View → PQ.View → Bool
  runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool
  rK : RecFull
  rP : RecFull
  depthReq : ℕ
  early : X → X
  salt : ℕ
  K : ℕ
  P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers
  T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P
  U : ToldLetters T₀
  /-- asked at VALID settings alone: at others `ModelWeights s` may be empty -/
  φ : (s : IntegerTransformer.Settings) → settingsAreValid s = true → A.Mat → ModelWeights s

/-- The honest side over a family of frames. -/
structure SideZ (fr : PublicFiles → FrameAt) where
  Shown : Type
  shown : (s : IntegerTransformer.Settings) → ModelWeights s → Shown
  Rand : Type
  sample : RandomizedAlgorithm Rand
  commit : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand →
    DeterministicAlgorithm Commitment
  Form : Type
  parse : (Z : PublicFiles) → List Token → List Token → Form → DeterministicAlgorithm
    (TypedProof (threeProtocolsWithFixedLinkAtFullSize (fr Z).A (relationsAndEncodingOfClaims (fr Z).A (fr Z).E) (fr Z).DK (fr Z).DP (fr Z).runK
      (fr Z).runP (fr Z).rK (fr Z).rP (fr Z).depthReq (fr Z).early (fr Z).salt) (fr Z).P)
  prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm Form

variable (fr : PublicFiles → FrameAt) (H : SideZ fr)

/-- Describe.lean's letters at the frame of Z. -/
def lettersAt (Z : PublicFiles) : DescribeLetters (fr Z).T₀ where
  U := (fr Z).U
  φ := (fr Z).φ
  Shown := H.Shown
  shown := H.shown
  Rand := H.Rand
  sample := H.sample
  commit := H.commit
  Form := H.Form
  parse := fun _ => H.parse Z
  prove := H.prove

/-- **THE VALUE: C, F, P, T AND THE EXTRACTOR READ Z.** -/
def describeZ : Description where
  C := fun Z => (describeFull (lettersAt fr H Z)).C Z
  F := fun Z => (describeFull (lettersAt fr H Z)).F Z
  P := fun Z => (describeFull (lettersAt fr H Z)).P Z
  More := List (Dig 256)
  readMore := fun Z c => (describeFull (lettersAt fr H Z)).readMore Z c
  T := fun Z c m => (describeFull (lettersAt fr H Z)).T Z c m
  extractor := fun Z => (describeFull (lettersAt fr H Z)).extractor Z
  Shown := H.Shown
  shown := H.shown
  Rand := H.Rand
  sample := H.sample
  commit := H.commit
  Form := H.Form
  parse := H.parse
  prove := H.prove

/-- At each Z its input is describeFull's at that Z's frame. -/
theorem input_describeZ (Z : PublicFiles) (c : Digest) (m : List (Dig 256)) :
    (describeZ fr H).input Z c m = (describeFull (lettersAt fr H Z)).input Z c m := rfl

/-- **ToldAt at describeZ**, field by field from `toldAt_describe` at the frame of Z. -/
def toldAt_describeZ (Z : PublicFiles) (s : IntegerTransformer.Settings)
    (newClaim : ModelWeights s → List Token → List Token → Prop)
    (B : ToldAt (describeFull (lettersAt fr H Z)) Z s newClaim) :
    ToldAt (describeZ fr H) Z s newClaim where
  c₀ := B.c₀
  m₀ := B.m₀
  T := B.T
  pair := B.pair
  claim := B.claim
  Wn := B.Wn
  Rno := B.Rno
  x₀ := B.x₀
  εs := B.εs
  q₀ := B.q₀
  φ := B.φ
  fits := B.fits
  core := B.core
  meaning := B.meaning
  noCoin := B.noCoin
  asks := B.asks
  once := B.once
  spare := B.spare
  word := B.word
  code := B.code
  reads := B.reads
  hq₀ := B.hq₀
  carries := B.carries

/-- **THE GOAL G7 AT describeZ**: every debt at every Z in scope that states exact match, at that
Z's frame; one eps over all. -/
theorem G7_describeZ_left (hA : BCHKS46At GF GE) (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (hk : ∀ Z, InScope Z = true → kThree .two (fr Z).DK frRds (fr Z).DP ≤ (fr Z).K)
    (wK : ∀ Z, InScope Z = true → (fr Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (fr Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (fr Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (fr Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize (fr Z).T₀))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize (fr Z).T₀))
    (claim : (Z : PublicFiles) → (fr Z).A.Mat → List Token → List Token → Prop)
    (meaning : ∀ Z, InScope Z = true → ∀ i (x' : List Token × List Token) a x,
      (fr Z).T₀.build x' a = some x → (∃ w, (soundnessAnalysisDataWithFixedLinkAtFullSize (fr Z).T₀).Rno i x w) →
        claim Z i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      pp.pol = Inst.Model.AcceptancePolicy.exact → ∀ i prompt output, claim Z i prompt output →
        ModelOutput (settingsOfRead pp) ((fr Z).φ (settingsOfRead pp) (valid_of_read hr) i) prompt
          output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      pp.pol = Inst.Model.AcceptancePolicy.exact → Parser.Within ((describeZ fr H).parse Z) honestBudget)
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      errDescribe (fr Z).T₀ (soundnessAnalysisDataWithFixedLinkAtFullSize (fr Z).T₀).εs t n ≤ eps t n) :
    G7 fun _ => describeZ fr H :=
  G7_of_told (fun _ => describeZ fr H) eps ceil
    (fun Z pp h₁ h₂ h₃ => toldAt_describeZ fr H Z (settingsOfRead pp) _
      (toldAt_describe (lettersAt fr H Z) Z (settingsOfRead pp) (valid_of_read h₂) _ (claim Z) _ _
          _ _
        (fun d => core_describe (lettersAt fr H Z) hA (hk Z h₁) (wK Z h₁) (dK Z h₁) (wP Z h₁)
          (dP Z h₁) (kS Z h₁) (pS Z h₁) Z d)
        (meaning Z h₁) (carries Z pp h₁ h₂ h₃)))
    ownParser fun Z _ h₁ _ _ t n => bound Z h₁ t n

/-- **THE GOAL G8 AT describeZ**, likewise. -/
theorem G8_describeZ_left (hA : BCHKS46At GF GE) (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (hk : ∀ Z, InScope Z = true → kThree .two (fr Z).DK frRds (fr Z).DP ≤ (fr Z).K)
    (wK : ∀ Z, InScope Z = true → (fr Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (fr Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (fr Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (fr Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize (fr Z).T₀))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize (fr Z).T₀))
    (claim : (Z : PublicFiles) → (fr Z).A.Mat → List Token → List Token → Prop)
    (meaning : ∀ Z, InScope Z = true → ∀ i (x' : List Token × List Token) a x,
      (fr Z).T₀.build x' a = some x → (∃ w, (soundnessAnalysisDataWithFixedLinkAtFullSize (fr Z).T₀).Rno i x w) →
        claim Z i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      ∀ i prompt output, claim Z i prompt output →
        Policy.MeetsPolicy (settingsOfRead pp) pp.pol
          ((fr Z).φ (settingsOfRead pp) (valid_of_read hr) i) prompt output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((describeZ fr H).parse Z) honestBudget)
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      errDescribe (fr Z).T₀ (soundnessAnalysisDataWithFixedLinkAtFullSize (fr Z).T₀).εs t n ≤ eps t n) :
    G8 fun _ => describeZ fr H :=
  G8_of_told (fun _ => describeZ fr H) eps ceil
    (fun Z pp h₁ h₂ => toldAt_describeZ fr H Z (settingsOfRead pp) _
      (toldAt_describe (lettersAt fr H Z) Z (settingsOfRead pp) (valid_of_read h₂) _ (claim Z) _ _
          _ _
        (fun d => core_describe (lettersAt fr H Z) hA (hk Z h₁) (wK Z h₁) (dK Z h₁) (wP Z h₁)
          (dP Z h₁) (kS Z h₁) (pS Z h₁) Z d)
        (meaning Z h₁) (carries Z pp h₁ h₂)))
    ownParser
    (fun Z pp h₁ h₂ => hext_describe (lettersAt fr H Z) Z (settingsOfRead pp) (valid_of_read h₂) _
        (claim Z)
      _ _ _ _ (fun d => core_describe (lettersAt fr H Z) hA (hk Z h₁) (wK Z h₁) (dK Z h₁) (wP Z h₁)
        (dP Z h₁) (kS Z h₁) (pS Z h₁) Z d) (meaning Z h₁) (carries Z pp h₁ h₂))
    fun Z _ h₁ _ t n => bound Z h₁ t n

/-- **G7 AT describeZ FROM G8's DEBTS ALONE**: by `g7_of_g8` (Ladder/Ties.lean:89): one claim, one
meaning, one «carries» serve both goals. -/
theorem G7_describeZ_by_G8 (h : G8 fun _ => describeZ fr H) : G7 fun _ => describeZ fr H :=
  g7_of_g8 _ h

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.input_describeZ
#print axioms VerifierAndGoals.Fit.toldAt_describeZ
#print axioms VerifierAndGoals.Fit.G7_describeZ_left
#print axioms VerifierAndGoals.Fit.G8_describeZ_left
#print axioms VerifierAndGoals.Fit.G7_describeZ_by_G8
