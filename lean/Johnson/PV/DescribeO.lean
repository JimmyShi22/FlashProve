-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/DescribeO.lean: the goals G8 and G7 at the family of Johnson/PV/DescribePolicy.lean with
an extractor that says none where no index is held.
`describeZO fr H phi`: the value. `phiO`, `claimPolicyO`, `meaningPolicyO`, `carriesPolicyO`: the
map from indices to weights, the claim, and the two hypotheses proved.
`G8_describeO_assuming_codes`: the theorem on codes a hypothesis. `G8_describeO`: it is taken from
`Cb.Gl.bchks46At` (Cb/Bridge/GlCodesProved.lean). `G7_describeO`: by `g7_of_g8`.
On the provenance of that theorem: the statement on codes is a theorem of this library whose proof
rests on files under lean/ThirdParty adapted from ArkLib and Mathlib (lean/LIMITS.md, L15).


The hypotheses of `G8_describeO`: numbers c a s v with a + s = 128, s <= 55, c <= 5/4, v <= 2^63; at
every Z in scope: he (the stated round error is at most c * 2^-a), hcnt (the compiled verifier's
count is at most v), hk wK dK wP dP (five tests on the rounds' data), keySound and proofSound (the
two whole files' protocols are sound), hb (the builder is `Flat.buildReq`), asks15 (the own parser
asks at most fifteen queries).
proofSound must give the relation at the files' own table and
policy.
A slot, no member: its letters are given no value here, and the description has run on no file. It
lays the coding of queries `mAll` (Johnson/PV/CutAll.lean), which is not the coding of the compiled
run. The full size alone. Conditional: no verifier that runs or ships is shown sound.

-/
import Johnson.PV.FitO
import Johnson.PV.Numbers
import Cb.Bridge.GlCodesProved

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
open Inst.Model.Layout (kRef hRef)
open Inst.Model (ScalesAndPolicy Lawful)
open scoped ENNReal

section General
variable (fr : PublicFiles → FrameAt) (H : SideZ fr)
  (φO : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
    (fr Z).A.Mat → Option (ModelWeights s))

/-- **THE VALUE**: describeZ with the extractor by bind. -/
def describeZO : Description :=
  { describeZ fr H with
    extractor := fun Z s commitment queryLog =>
      if h : settingsAreValid s = true then
        ((toldOf (atZ (fr Z).U Z)).extractor commitment queryLog).bind (φO Z s h)
      else none }

/-- ToldAtO at it, field by field from `toldAt_describe` at the frame of Z (taken at the claim
«True» on weights: its own φ and carries are not read). -/
def toldAtO_describeZ (Z : PublicFiles) (s : IntegerTransformer.Settings) (hv : settingsAreValid s = true)
    (newClaim : ModelWeights s → List Token → List Token → Prop)
    (claim : (fr Z).A.Mat → List Token → List Token → Prop) (Wn : Type)
    (Rno : (fr Z).A.Mat → (fr Z).X → Wn → Prop) (x₀ : (fr Z).X) (εs : ℝ≥0∞)
    (core : ∀ d, CompilerSoundnessConditions ((toldAtZ (lettersAt fr H Z) Z).beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, (fr Z).T₀.build x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (carries : ∀ i prompt output, claim i prompt output →
      ∃ w, φO Z s hv i = some w ∧ newClaim w prompt output) :
    ToldAtO (describeZO fr H φO) Z s newClaim :=
  let B := toldAt_describe (lettersAt fr H Z) Z s hv (fun _ _ _ => True) claim Wn Rno x₀ εs core
    meaning (fun _ _ _ _ => trivial)
  { c₀ := B.c₀, m₀ := B.m₀, T := B.T, pair := B.pair, claim := B.claim, Wn := B.Wn, Rno := B.Rno
    x₀ := B.x₀, εs := B.εs, q₀ := B.q₀, φ := φO Z s hv, ψ := B.φ, fits := B.fits, core := B.core
    meaning := B.meaning, noCoin := B.noCoin, asks := B.asks, once := B.once, spare := B.spare
    word := B.word, code := B.code, reads := B.reads, hq₀ := B.hq₀, carries := carries }

/-- **THE GOAL G8 AT describeZO.** -/
theorem G8_describeZO_left (hA : BCHKS46At GF GE) (eps : ℕ → ℕ → ℝ≥0∞)
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
        ∃ w, φO Z (settingsOfRead pp) (valid_of_read hr) i = some w ∧
          Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((describeZO fr H φO).parse Z) honestBudget)
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      errDescribe (fr Z).T₀ (soundnessAnalysisDataWithFixedLinkAtFullSize (fr Z).T₀).εs t n ≤ eps t n) :
    G8 fun _ => describeZO fr H φO :=
  G8_of_toldO (fun _ => describeZO fr H φO) eps ceil
    (fun Z pp h₁ h₂ => toldAtO_describeZ fr H φO Z (settingsOfRead pp) (valid_of_read h₂) _ (claim
        Z)
      _ _ _ _ (fun d => core_describe (lettersAt fr H Z) hA (hk Z h₁) (wK Z h₁) (dK Z h₁) (wP Z h₁)
        (dP Z h₁) (kS Z h₁) (pS Z h₁) Z d) (meaning Z h₁) (carries Z pp h₁ h₂))
    ownParser
    (fun Z pp _ h₂ => by
      funext commitment queryLog
      show (if h : settingsAreValid (settingsOfRead pp) = true then
          ((toldOf (atZ (fr Z).U Z)).extractor commitment queryLog).bind
            (φO Z (settingsOfRead pp) h) else none) = _
      rw [dif_pos (valid_of_read h₂)]
      rfl)
    fun Z _ h₁ _ t n => bound Z h₁ t n

end General

/-! ## At the files' own policy -/

/-- The weights, at valid settings, of the index that the matrix holds; NONE where it holds none. -/
def phiO {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
    {rows cols : ℕ} (M : Fin rows → Fin cols → Flat.GE) : Option (ModelWeights settings) :=
  (Flat.indexOf M).map (weightsOfIndex valid)

/-- The claim on a decoded matrix: IT HOLDS AN INDEX, and the output meets the table's policy at
that index's weights. -/
def claimPolicyO (pp : ScalesAndPolicy) (lawful : Lawful pp) {rows cols : ℕ}
    (M : Fin rows → Fin cols → Flat.GE) (prompt output : List Token) : Prop :=
  ∃ j, Flat.indexOf M = some j ∧
    Policy.MeetsPolicy (settingsOf (Cm.Scales.of pp)) pp.pol
      (weightsOfIndex (settingsAreValid_settingsOf (Cm.lawful_of lawful)) j) prompt output

section
variable (N : MatrixNums) (pp : ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : Flat.Req × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : Flat.Req → Flat.Req) (salt K : ℕ)
  (P : (threeProtocolsWithFixedLinkAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) (relationsAndEncodingOfClaims _ E) DK DP runK runP rK rP
    depthReq early salt).Provers)

/-- The meaning for `claimPolicyO`: by the lines of `meaningPolicyOfFull`. -/
theorem meaningPolicyO (lawful : Lawful pp) (hr : N.rows ≤ hRef)
    (hc : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DK DP runK runP rK rP
      depthReq early salt K P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a) :
    ∀ i (x' : List Token × List Token) a x, T.build x' a = some x →
      (∃ w, (soundnessAnalysisDataWithFixedLinkAtFullSize T).Rno i x w) → claimPolicyO pp lawful i x'.1 x'.2 := by
  rintro i x' a x hbx ⟨_, hw⟩
  obtain ⟨j, hj, tr, ht⟩ := hw.2
  exact ⟨j, Flat.indexOf_eq hr hc hj,
    OnBytes.Road.L5.sound_ledger (Cm.lawful_of lawful) _ rfl lawful.polOK j x' a x.1
      (Flat.buildReq_some ((hb x' a).symm.trans hbx)) ⟨tr, ht⟩⟩

end

/-- Where the claim holds, phiO says some, with the goal's sentence at what it says. -/
theorem carriesPolicyO {pp pp' : ScalesAndPolicy} (e : pp' = pp) (lawful' : Lawful pp')
    (valid : settingsAreValid (settingsOf (Cm.Scales.of pp)) = true) {rows cols : ℕ}
    (M : Fin rows → Fin cols → Flat.GE) (prompt output : List Token) :
    claimPolicyO pp' lawful' M prompt output →
      ∃ w, phiO valid M = some w ∧
        Policy.MeetsPolicy (settingsOf (Cm.Scales.of pp)) pp.pol w prompt output := by
  subst e
  rintro ⟨j, hj, hm⟩
  exact ⟨_, by unfold phiO; rw [hj]; rfl, hm⟩

/-- At a matrix that holds no index phiO says none. -/
theorem phiO_none {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) {rows cols : ℕ} (M : Fin rows → Fin cols → Flat.GE)
    (h : ¬ Flat.InRange M) : phiO valid M = none := by
  unfold phiO Flat.indexOf
  rw [dif_neg h]
  rfl

/-- **THE GOAL G8, THE THEOREM ON CODES AN EXPLICIT HYPOTHESIS (hA)**: all else that is proved is
laid in; the extractor says none where no index is held. -/
theorem G8_describeO_assuming_codes (g : (Z : PublicFiles) → FramePol numsRef (ppAtFiles Z.pol Z.KL))
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
    G8 fun _ => describeZO (fun Z => (g Z).toFrame) H (fun _ _ valid => phiO valid) :=
  G8_describeZO_left (fun Z => (g Z).toFrame) H (fun _ _ valid => phiO valid) hA (epsFrame s v)
    (fun t n ht hn => ceil_of_numbers s v hs hv t n ht hn) hk wK dK wP dP kS pS
    (fun Z => claimPolicyO (ppAtFiles Z.pol Z.KL) (lawful_ppAtFiles Z.pol Z.KL))
    (fun Z h₁ => meaningPolicyO numsRef (ppAtFiles Z.pol Z.KL) (g Z).E (g Z).DK (g Z).DP (g Z).runK
      (g Z).runP (g Z).rK (g Z).rP (g Z).depthReq (g Z).early (g Z).salt (g Z).K (g Z).P
      (lawful_ppAtFiles Z.pol Z.KL) numsRef_fits.1 numsRef_fits.2 (g Z).T₀ (hb Z h₁))
    (fun _ _ _ hr i prompt output h =>
      carriesPolicyO (ppAtFiles_of_read hr) _ (valid_of_read hr) i prompt output h)
    (fun Z _ h₁ _ => within_mono
      ((describeZO (fun Z => (g Z).toFrame) H (fun _ _ valid => phiO valid)).parse Z)
      fifteen_le_honestBudget (asks15 Z h₁))
    (fun Z h t n => bound_of_numbers (g Z).T₀.W _ c a s v has (he Z h) hc
      (le_of_eq_of_le (tVC_wireOfFull _ _ _ _ _ _ _ _ _ _ _ _ _ _) (hcnt Z h)) t n)

/-- **The goal G8, the theorem on codes paid by the call** (`Cb.Gl.bchks46At`,
Cb/Bridge/GlCodesProved.lean:20). On its provenance: «the statement on codes is a theorem of this
library whose proof rests on files under lean/ThirdParty adapted from ArkLib and Mathlib
(lean/LIMITS.md, L15)».

The form with hA explicit stands beside it: `G8_describeO_assuming_codes`. -/
theorem G8_describeO (g : (Z : PublicFiles) → FramePol numsRef (ppAtFiles Z.pol Z.KL))
    (H : SideZ fun Z => (g Z).toFrame)
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
    G8 fun _ => describeZO (fun Z => (g Z).toFrame) H (fun _ _ valid => phiO valid) :=
  G8_describeO_assuming_codes g H Cb.Gl.bchks46At c a s v has hs hc hv he hcnt hk wK dK wP dP kS pS
      hb
    asks15

/-- **THE GOAL G7 THERE**, by `g7_of_g8`. -/
theorem G7_describeO (g : (Z : PublicFiles) → FramePol numsRef (ppAtFiles Z.pol Z.KL))
    (H : SideZ fun Z => (g Z).toFrame)
    (h : G8 fun _ => describeZO (fun Z => (g Z).toFrame) H (fun _ _ valid => phiO valid)) :
    G7 fun _ => describeZO (fun Z => (g Z).toFrame) H (fun _ _ valid => phiO valid) := g7_of_g8 _ h

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.G8_describeZO_left
#print axioms VerifierAndGoals.Fit.meaningPolicyO
#print axioms VerifierAndGoals.Fit.carriesPolicyO
#print axioms VerifierAndGoals.Fit.phiO_none
#print axioms VerifierAndGoals.Fit.G8_describeO_assuming_codes
#print axioms VerifierAndGoals.Fit.G8_describeO
#print axioms VerifierAndGoals.Fit.G7_describeO
