-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean: a twin, made by program, of a file that is not in this library,
  over DescriptionDataAtFiles | DescriptionFields | descriptionOfFields (Johnson/Goal/Tie/DescriptionOnDecodedProof.lean | DescribeT.lean: DescriptionDataAtFiles has the
  field dec behind runP; its types are the D-names at dsF xsF dec) and
  Johnson/Flat/Told/Dec/TAtLaws.lean.
The original is not in this library. The declared names are the original's. Where this twin
  parts: compilerSoundnessConditions_layoutsByPublicReading has entrySound (eS) as a premise in the theorem on codes' place, hk at
  «[]», and the four tests on dsF's numbers. All else, who reads each letter, and every limit: as
  the original's head says.
That head's sentences on this, word for word, since that file is not in this library (they are
  written of the original's statements, in its names; «TAtLaws.lean's head»: see
  Johnson/Flat/Told/Dec/TAtLaws.lean's head):
  Every proof is a call of the law at letters. All limits of TAtLaws.lean's head stand; no S is
    built here.
This variant: DescriptionDataAtFiles has a field G : FilesParameters XF RecFull: «S.G» stands where a
  variant that is not in this library has «(GF Zk)»; nothing else parts.
`DescriptionDataAtFiles` has the field `it` (the request's item): the law is called
as «S.hStar S.it». `DescriptionDataAtFiles.layoutsByPublicReadingWithParameterBytes`: the record with the
parameter bytes a letter (`toldDBy`, Johnson/Flat/Told/Dec/TAtBy.lean); `extractor_layoutsByPublicReadingWithParameterBytes`.
No soundness is claimed.
-/
import Johnson.Flat.Told.Dec.TAtBy
import Johnson.Goal.Tie.DescriptionOnDecodedProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Maker.Page (Pd3 kindsAndWorkBelow256)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR tAt mOneAt tD toldD)
open PV.EntryFive (dsF xsF)

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

section
attribute [local irreducible] LPFD.Full.mOneAt

/-- **D⋆'s FAMILY IS THE FAMILY d ↦ tAt … d OF Johnson/Flat/Told/Dec/TAt.lean**, at S's letters and
    G := S.G: by unfolding. -/
theorem DescriptionDataAtFiles.tOf_tD (c : Digest) (m : List (Dig 256)) : S.inputFieldsAtReadings c m = tD S.A S.E S.G S.DK S.DP
    S.runK S.runP S.dec S.P S.hStar S.it S.sR S.hDK S.hDP S.hK S.N S.d₀ (c, m) := rfl

end

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8

/-- **THE VALUE.** -/
def DescriptionDataAtFiles.layoutsByPublicReading : LayoutsByPublicReading (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)) := toldD S.A S.E S.G S.DK S.DP S.runK
    S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀)

/-- **The value, the parameter bytes a letter**: so that its text names no hash function. -/
def DescriptionDataAtFiles.layoutsByPublicReadingWithParameterBytes (par : ByteArray → List ByteArray) : LayoutsByPublicReading (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)) :=
  LPFD.Full.toldDBy S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay
    par S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀)

/-- The extractor does not read the parameter bytes: by definition. -/
theorem DescriptionDataAtFiles.extractor_layoutsByPublicReadingWithParameterBytes (par : ByteArray → List ByteArray) :
    (S.layoutsByPublicReadingWithParameterBytes c₀ m₀ par).extractor = (S.layoutsByPublicReading c₀ m₀).extractor := rfl

/-- **THE RECORD's INPUT AT d IS D⋆'s INPUT AT d.** -/
theorem DescriptionDataAtFiles.at_layoutsByPublicReading (d : D8) : (S.layoutsByPublicReading c₀ m₀).at d = innerCompilerInputAtFullSize (S.inputFieldsAtReadings d.1 d.2) :=
  LPFD.Full.at_toldD S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay
      S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀) d

/-! ## The six added premises -/

theorem layoutsByPublicReading_noCoin : (S.layoutsByPublicReading c₀ m₀).Pub.NoCoin := LPFD.Full.noCoinD S.A S.E S.G S.DK S.DP S.runK
    S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀)

theorem layoutsByPublicReading_asks : (S.layoutsByPublicReading c₀ m₀).Pub.AsksIn fun _ s => (S.layoutsByPublicReading c₀ m₀).Pt s := LPFD.Full.asksD
    S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay S.sR S.hDK S.hDP
    S.hK S.N S.d₀ (c₀, m₀)

theorem layoutsByPublicReading_once : NoRepeat (S.layoutsByPublicReading c₀ m₀).Pub := LPFD.Full.onceD S.A S.E S.G S.DK S.DP S.runK
    S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀)

/-- **«spare».** -/
theorem layoutsByPublicReading_spare : ∀ d s, (S.layoutsByPublicReading c₀ m₀).Pt s → IsOther ((S.layoutsByPublicReading c₀ m₀).m d) s :=
    LPFD.Full.spareD S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay
    S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀)

/-- **«word».** -/
theorem layoutsByPublicReading_word : ∀ d d', (S.layoutsByPublicReading c₀ m₀).part d = (S.layoutsByPublicReading c₀ m₀).part d' →
    (extractorOverOneHashFunction ((S.layoutsByPublicReading c₀ m₀).m d) (indexExtractorAtRootAndOutOfDomainSample (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout)).Ei =
      (extractorOverOneHashFunction ((S.layoutsByPublicReading c₀ m₀).m d') (indexExtractorAtRootAndOutOfDomainSample (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout)).Ei :=
          LPFD.Full.wordD S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL
          Zk.lay S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀)

/-- **«code».** -/
theorem layoutsByPublicReading_code : ZKCP.CodeIsOneToOne (S.layoutsByPublicReading c₀ m₀).encT := LPFD.Full.codeD S.A S.E S.G S.DK
    S.DP S.runK S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay S.sR S.hDK S.hDP S.hK S.N S.d₀
    (c₀, m₀)

/-- Every pair (told part, key) has a code. -/
theorem layoutsByPublicReading_total (key : Dig 256 × KeyRoot 256 (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol) : (S.layoutsByPublicReading c₀
                                                           m₀).encT key ≠ none :=
  LPFD.Full.totalD S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay
      S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀) key

set_option maxRecDepth 20000 in
/-- **THE FIFTEEN AT EVERY d**, from keySound, entrySound, proofSound at (S.inputFieldsAtReadings c₀ m₀)'s names. -/
theorem compilerSoundnessConditions_layoutsByPublicReading (hk : kThree .two S.DK [] S.DP ≤ KF S.DK S.DP)
    (bL : ∀ d ∈ dsF, (bsRound .two d.entry d.kind).b ≤ KF S.DK S.DP) (wLk : ∀ d ∈ dsF, d.entry.work
        ≤ 64)
    (own : ∀ d ∈ dsF, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ dsF, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : S.DK.workFit = true) (dK : S.DK.depthFit = true) (wP : S.DP.workFit = true)
    (dP : S.DP.depthFit = true) (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀ m₀)))
    (eS : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀ m₀)))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀ m₀))) (d : (S.layoutsByPublicReading c₀ m₀).D) :
    CompilerSoundnessConditions ((S.layoutsByPublicReading c₀ m₀).beside (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀ m₀)).Wn (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀
                                                                                                m₀)).Rno
                          (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀ m₀)).x₀ (soundnessAnalysisDataAtFullSize (S.inputFieldsAtReadings c₀ m₀)).εs d) :=
  LPFD.Full.coreD S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it Zk.pol Zk.KL Zk.lay
      S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀) hk bL wLk own dL wK dK wP dP kS eS pS d

end FlashProve

#print axioms FlashProve.DescriptionDataAtFiles.tOf_tD
#print axioms FlashProve.DescriptionDataAtFiles.layoutsByPublicReading
#print axioms FlashProve.DescriptionDataAtFiles.layoutsByPublicReadingWithParameterBytes
#print axioms FlashProve.DescriptionDataAtFiles.extractor_layoutsByPublicReadingWithParameterBytes
#print axioms FlashProve.DescriptionDataAtFiles.at_layoutsByPublicReading
#print axioms FlashProve.layoutsByPublicReading_noCoin
#print axioms FlashProve.layoutsByPublicReading_asks
#print axioms FlashProve.layoutsByPublicReading_once
#print axioms FlashProve.layoutsByPublicReading_spare
#print axioms FlashProve.layoutsByPublicReading_word
#print axioms FlashProve.layoutsByPublicReading_code
#print axioms FlashProve.layoutsByPublicReading_total
#print axioms FlashProve.compilerSoundnessConditions_layoutsByPublicReading
