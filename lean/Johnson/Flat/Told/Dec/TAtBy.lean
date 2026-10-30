-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/Dec/TAtBy.lean: the told record over LPFD.Full.tAt, the parameter bytes a letter:
`toldDBy … e := toldFamBy (famD … e) par` (Johnson/Flat/Told/FamilyBy.lean), with the laws of
Johnson/Flat/Told/Dec/TAtLaws.lean at it. Made by program from that file: each name has «By» behind
it and takes par : ByteArray → List ByteArray behind lay. So its text names no hash function (a
walk's print, no theorem).
`toldD_eq_by`: the record of TAtLaws.lean is this one at `par7 recordGround pol KL lay`: by
definition. `readingDBy`: where par gives at most n members the public reading asks at most n + 1
strings.
Limits: those of TAtLaws.lean. `coreDBy` stands under that file's `set_option maxRecDepth 20000 in`.
No soundness is claimed.
-/
import Johnson.Flat.Told.Dec.TAtLaws
import Johnson.Flat.Told.FamilyBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open OnBytes.Maker.Page (Pd3 kindsAndWorkBelow256)
open OnBytes.K.Arm.Pub
open PV.EntryFive (dsF xsF)


section Fam
variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull →
        PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (pol KL lay :
        ByteArray)
    (par : ByteArray → List ByteArray) (sR : ℕ)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP
                                    + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
        (saltG G) P) (d₀ : Dig 256)


/-- **THE VALUE, AT LETTERS.** -/
def toldDBy (e : D8) : LayoutsByPublicReading (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK
                                N d₀ e)) :=
  toldFamBy (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) par

/-- The record of TAtLaws.lean is this one at `par7 recordGround pol KL lay`: by definition. -/
theorem toldD_eq_by (e : D8) :
    toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e =
      toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay (par7 OnBytes.Tie.recordGround pol KL
          lay)
        sR hDK hDP hK N d₀ e := rfl

/-- Where par gives at most n members, the public reading asks at most n + 1 strings. -/
theorem readingDBy (e : D8) (n : ℕ) (hn : ∀ c, (par c).length ≤ n) :
    (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e).Pub.QueryBound
      (n + 1) :=
  famBy_reading (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) par n hn

/- From here on Lean compares the names tD and pub8 and does not unfold them. -/
attribute [local irreducible] tD pub8

/-- **THE RECORD's INPUT AT d IS THE FRAME's INPUT AT THE FAMILY's MEMBER AT d.** -/
theorem at_toldDBy (e d : D8) : (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK
    hDP hK N d₀ e).at d = innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀
                 d) := by
  rw [tD_fam A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e d]
  exact at_toldFamBy (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) par d

theorem noCoinDBy (e : D8) : (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP
    hK N d₀ e).Pub.NoCoin := famBy_noCoin (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK
    hDP hK N d₀ e) par

theorem asksDBy (e : D8) : (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK
    N d₀ e).Pub.AsksIn fun _ s => (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK
    hDP hK N d₀ e).Pt s := famBy_asks (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP
    hK N d₀ e) par

theorem onceDBy (e : D8) : NoRepeat (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR
    hDK hDP hK N d₀ e).Pub := famBy_once (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK
    hDP hK N d₀ e) par

/-- **«spare».** -/
theorem spareDBy (e : D8) : ∀ d s, (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK
    hDP hK N d₀ e).Pt s → IsOther ((toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK
    hDP hK N d₀ e).m d) s := fun d s hs =>
  mOneAt_isOther169 A E G (digToBytes d.1) (size_digToBytes d.1) DK DP runK runP dec P h₀ it sR
    (PV.RunArgsF.pdLOf (d.2.map digToBytes)) (PV.RunArgsF.pd3At (d.2.map digToBytes) 4)
        (PV.RunArgsF.pd3At (d.2.map digToBytes) 1)
    hDK hDP hK s hs

/-- **«word».** -/
theorem wordDBy (e : D8) : ∀ d d', (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK
    hDP hK N d₀ e).part d = (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK
    N d₀ e).part d' →
    (extractorOverOneHashFunction ((toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e).m d)
        (indexExtractorAtRootAndOutOfDomainSample (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀
                                                  e)).queryLayout)).Ei =
      (extractorOverOneHashFunction ((toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e).m
                                d') (indexExtractorAtRootAndOutOfDomainSample (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N
                                                                          d₀ e)).queryLayout)).Ei := by
  rintro ⟨c, l⟩ ⟨c₁, l₁⟩ (h : c = c₁)
  subst h
  exact mOneAt_word A E G (digToBytes c) (size_digToBytes c) DK DP runK runP dec P h₀ it sR
    (PV.RunArgsF.pdLOf (l.map digToBytes)) (PV.RunArgsF.pd3At (l.map digToBytes) 4)
        (PV.RunArgsF.pd3At (l.map digToBytes) 1)
    hDK hDP hK
    (PV.RunArgsF.pdLOf (l₁.map digToBytes)) (PV.RunArgsF.pd3At (l₁.map digToBytes) 4)
        (PV.RunArgsF.pd3At (l₁.map digToBytes) 1)
    (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)

section Sealed2
attribute [local irreducible] mD PV.EncId.encF PV.MFull.cfgF

/-- **«code».** -/
theorem codeDBy (e : D8) : ZKCP.CodeIsOneToOne (toldDBy A E G DK DP runK runP dec P h₀ it pol KL
    lay par sR hDK hDP hK N d₀ e).encT := codeFamD A E G DK DP runK runP dec P h₀ it pol KL lay sR
    hDK hDP hK N d₀ e

/-- Every pair (told part, key) has a code. -/
theorem totalDBy (e : D8) (key : Dig 256 × KeyRoot 256 (innerCompilerInputAtFullSize (tD A E G DK DP runK runP
                 dec P h₀ it sR hDK hDP hK N d₀ e)).protocol) : (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay
                        par sR hDK hDP hK N d₀ e).encT key ≠ none :=
  PV.EncId.encF_total (restOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG
                            G).logLeaves G.early (saltG G) P) key

set_option maxRecDepth 20000 in
/-- **THE FIFTEEN AT EVERY d**, from keySound, entrySound, proofSound at the member e's names. -/
theorem coreDBy (e : D8) (hk : kThree .two DK [] DP ≤ KF DK DP)
    (bL : ∀ d ∈ dsF, (bsRound .two d.entry d.kind).b ≤ KF DK DP) (wLk : ∀ d ∈ dsF, d.entry.work ≤
        64)
    (own : ∀ d ∈ dsF, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ dsF, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true) (dP : DP.depthFit =
        true)
    (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N
                                                     d₀ e)))
    (eS : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N
                                                     d₀ e)))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N
                                                     d₀ e)))
    (d : (toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e).D) :
    CompilerSoundnessConditions ((toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e).beside
                            (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).Wn
                          (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).Rno
                          (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).x₀
                          (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).εs d) :=
  core_toldFamBy (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) par
      (codeFamD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) hk bL wLk own dL
      wK dK wP dP kS eS pS d

/-- **«fits», at letters**: innerCompiledVerifier at the frame's input at the family's member at d IS innerCompiledVerifier
    at the record's input at d. -/
theorem fitsDBy (e d : D8) (commitment : Commitment) (prompt output : List Token)
    (proof : VerifierAndGoals.TypedProof (FsAtR A E G DK DP runK runP dec) P) :
    innerCompiledVerifier (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ d))
        commitment prompt output proof =
      innerCompiledVerifier ((toldDBy A E G DK DP runK runP dec P h₀ it pol KL lay par sR hDK hDP hK N d₀ e).at
                      d) commitment prompt output proof :=
  congrArg (fun T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG
                                  G).logLeaves G.early (saltG G) (KF DK DP) P =>
    innerCompiledVerifier (innerCompilerInputAtFullSize T) commitment prompt output proof) (tD_fam A E G DK DP runK runP dec
                                 P h₀ it pol KL lay sR hDK hDP hK N d₀ e d)

end Sealed2

end Fam

end LPFD.Full

#print axioms LPFD.Full.toldDBy
#print axioms LPFD.Full.toldD_eq_by
#print axioms LPFD.Full.readingDBy
#print axioms LPFD.Full.at_toldDBy
#print axioms LPFD.Full.noCoinDBy
#print axioms LPFD.Full.asksDBy
#print axioms LPFD.Full.onceDBy
#print axioms LPFD.Full.spareDBy
#print axioms LPFD.Full.wordDBy
#print axioms LPFD.Full.codeDBy
#print axioms LPFD.Full.totalDBy
#print axioms LPFD.Full.coreDBy
#print axioms LPFD.Full.fitsDBy
