-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/SoundAtThe.lean: **the goal on soundness under the files' policy, G8
  (Ladder.lean), at the one closed description with the terms laid in**: `theBound K` := fun _ =>
  (descriptionOfDataOnBytes flashProveData).withTerms (theTerms K) (Johnson/Goal/Conditions/BindsAtThe.lean): the very
  description of which G9 | G9bits are shown there, at the same extractor. A conditional.
  claimThe Z        the claim on a decoded matrix: it holds an index, and the output meets the
    files' own policy at that index's weights (claimPolicyO, Johnson/Flat/Dec/PolicyAtFrame.lean)
  meaning_the «meaning» at the description's own letters: proved (meaningPolicyOD: the claims
    are claimsReqAt at numsRef and the files' own table; the builder is Flat.buildReq, by rfl)
  phiO_one | claimPolicyO_one   the library holds two texts of phiO and of claimPolicyO
    (Johnson/Flat/Dec/PolicyAtFrame.lean; Johnson/PV/DescribeO.lean): they are one, by rfl: so
    soundness and binding stand at one φ
  carries_the «carries» at phiThe: proved (carriesPolicyO, Johnson/PV/DescribeO.lean: at the
    very phiO of which binding's section_backO speaks)
  **G8_theBound**   G8 (theBound K), at every K
The hypotheses of G8_theBound, all. On soundness, at every Z in scope where protocolDataWellFormed says yes: kS ·
eS ·
  pS: keySound · entrySound · proofSound (Johnson/Top/InnerCompiledVerifier.lean) at the description's named
  side: here sits all the weight: they are hypotheses here. On numbers: he: the
  named side's εs ≤ c · 2^-a, with a + s = 128 · s ≤ 55 · c ≤ 5/4. A letter: ψ (a total filler for
  an auxiliary system's honest side; no statement reads it).
Gone against G8_theDescription (Johnson/Goal/Description/JointD.lean): hext (the extractor is the told record's,
  then phiThe, by withTerms: ToldSoundTerms.lean) · bound | ceil (at eps := epsFrame s theQueries:
  ToldBound.lean) · the nine on numbers and «only where protocolDataWellFormed says yes» (NumbersAtThe.lean) ·
  claim | meaning | carries (here) · ownParser (the description's own parser asks once:
  parseDec_honest).
Who reads each letter. K: the honest side alone: soundness reads none of it. c a s: the closed
  error's level. ∃: claimThe's «∃ j, indexOf M = some j ∧ …»: j is indexOf's own value; carries' «∃
  w»: w is phiThe's own value: nothing that the verifier reads is chosen.
Does not show. No soundness of any verifier: a conditional whose three premises on soundness are
  not proved here; where they are proved, and how far: the head of Johnson/Goal/TopOfThree.lean,
  limit (1). The named side is hollow
  (Johnson/Goal/Description/Named.lean;
  who reads it: TopOfThree.lean, limit
  (3)).
  Where protocolDataWellFormed says no the verifier
  refuses all: true and empty there: it counts only beside «protocolDataWellFormed says yes at the release's files»
  (at the written copies a theorem, AtFullSide/Top/; as bytes an evaluation; not shown in this
  file). The ceiling is one quarter: no security level. What sits in the three seats is told in
  Johnson/Goal/Description/KeyFold.lean, ProofFold.lean and LinkDec.lean.
  (Of `verify` itself, at the error `soundnessErrorInQueries`, with no such premises: `g8bits_of_verify`,
  Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean.)
  The public files are fixed
  before the hash function is drawn; the description's T reaches the format's hashes by name.
  theBound K is VerifierAndGoals.theDescription only if that name is laid so.
The silly members. The theorem speaks of one description; at its gates shut (protocolDataWellFormed says no) it is
  «no to all». «Yes to all» is no member.
No soundness is claimed in this file.
-/
import Johnson.Goal.Conditions.ToldSoundTerms
import Johnson.Goal.Conditions.ToldBound
import Johnson.Goal.Conditions.BindsAtThe
import Johnson.Flat.Dec.PolicyAtFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF GF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8 theCoding theKeyData
  theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate theProvers theNamed LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins)

/-- The two texts of the way from a matrix to weights are one (Johnson/Flat/Dec/PolicyAtFrame.lean; Johnson/PV/DescribeO.lean): so soundness here and binding (BindsAtThe.lean) stand AT ONE φ. -/
theorem phiO_one {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true) {rows cols : ℕ}
    (M : Fin rows → Fin cols → Flat.GE) :
    VerifiableInference.OnPublicFiles.phiO valid M = VerifierAndGoals.Fit.phiO valid M := rfl

/-- So are the two texts of the claim. -/
theorem claimPolicyO_one (pp : Inst.Model.ScalesAndPolicy) (lawful : Inst.Model.Lawful pp) {rows cols : ℕ}
    (M : Fin rows → Fin cols → Flat.GE) (prompt output : List Token) :
    VerifiableInference.OnPublicFiles.claimPolicyO pp lawful M prompt output =
      VerifierAndGoals.Fit.claimPolicyO pp lawful M prompt output := rfl

/-- The claim on a decoded matrix, at the files' own policy. -/
def claimThe (Z : PublicFiles) : (dataAtFiles flashProveData Z).A.Mat → List Token → List Token → Prop :=
  VerifiableInference.OnPublicFiles.claimPolicyO (ppAtFiles Z.pol Z.KL) (lawful_ppAtFiles Z.pol Z.KL)

/-- **«meaning» at the description's own letters.** -/
theorem meaning_the (Z : PublicFiles) : ∀ i (x' : List Token × List Token) a x,
    ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).build x' a = some x →
      (∃ w, (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])).Rno i x w) → claimThe Z i x'.1 x'.2 :=
  meaningPolicyOD numsRef (ppAtFiles Z.pol Z.KL) (dataAtFiles flashProveData Z).E (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP dsF xsF
    (dataAtFiles flashProveData Z).dec _ _ _ _ _ _ (dataAtFiles flashProveData Z).P (lawful_ppAtFiles Z.pol Z.KL) numsRef_fits.1 numsRef_fits.2
    ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []) (fun _ _ => rfl)

/-- **«carries» at phiThe.** -/
theorem carries_the (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (i : (dataAtFiles flashProveData Z).A.Mat)
    (prompt output : List Token) (h : claimThe Z i prompt output) :
    ∃ w, phiThe Z (settingsOfRead pp) i = some w ∧
      Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output := by
  unfold phiThe
  rw [dif_pos (valid_of_read hr)]
  have h' : VerifierAndGoals.Fit.claimPolicyO (ppAtFiles Z.pol Z.KL) (lawful_ppAtFiles Z.pol Z.KL) i prompt output := h
  exact VerifierAndGoals.Fit.carriesPolicyO (ppAtFiles_of_read hr) _ (valid_of_read hr) i prompt output h'

/-- **THE STORED G8 AT THE DESCRIPTION WITH THE TERMS LAID IN, AT EVERY K: FROM THE THREE HYPOTHESES ON SOUNDNESS WHERE THE TEST SAYS YES, AND ONE INEQUALITY ON εs.** -/
theorem G8_theBound
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → ModelWeights s)
    (c : ℝ≥0∞) (a s : ℕ) (has : a + s = 128) (hs : s ≤ 55) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (he : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).N.εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹)
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G8 (theBound K) :=
  have e := entryFit_of_test entryFitB_dsFull_140
  G8_descriptionOfFields_withTerms (dataAtFiles flashProveData) (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀) allZeroDigest []
    phiThe backThe K.ri K.sl K.b₀ K.proveT K.Rand K.sample
    (fun Z => coinsAnchor Z (K.shape Z) (K.gen Z)) K.prove ψ (epsFrame s theQueries)
    (frameError_le_ceiling s theQueries hs (by unfold theQueries; norm_num))
    (fun Z _ => (parts_the Z).hk) (fun Z _ => (parts_the Z).hE.bL) e.wLk e.own e.dL
    (fun Z _ => (parts_the Z).wK) (fun Z _ => (parts_the Z).dK) (fun Z _ => (parts_the Z).wP)
    (fun Z _ => (parts_the Z).dP)
    (fun Z h => keySound_theLay Z allZeroDigest [] (kS Z h)) (fun Z h => entrySound_theLay Z allZeroDigest [] (eS Z h))
    (fun Z h => proofSound_theLay Z allZeroDigest [] (pS Z h)) claimThe (fun Z _ => meaning_the Z)
    (fun Z pp _ hr => carries_the Z pp hr)
    (fun Z _ _ _ => parseDec_honest (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀ Z)
    (fun Z h t n => errorBound_descriptionDataAtFiles (dataAtFiles flashProveData Z) allZeroDigest [] theQueries (fit_theLay Z) c a s has (he Z h) hc t n)

end FlashProve

#print axioms FlashProve.phiO_one
#print axioms FlashProve.claimPolicyO_one
#print axioms FlashProve.meaning_the
#print axioms FlashProve.carries_the
#print axioms FlashProve.G8_theBound
