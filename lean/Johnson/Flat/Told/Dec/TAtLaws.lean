-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/Dec/TAtLaws.lean: a twin, made by program, of a file that is not in this library,
  over tAt over the D-names (Johnson/Top/Fire/Code/TieAtValues.lean:
  tAt · tAtR · vAtR · mOneAt take the entry file's decision
  «dec» behind runP; ds xs are pinned at PV.EntryFive.dsF | xsF; the coding is PV.MFull.mFOneD) and
  the frame with the entry file's three letters (InnerCompilerInputAndAnalysisFieldsAtFullSize).
The declared names are the original's (LPFD.Full.tD · toldD · spareD …), as TieAtValues.lean's are.
  The original is not in this library. Where this twin parts: coreD has
  entrySound (eS) as a premise in the theorem on codes' place, hk at «[]», and the four tests on
  dsF's numbers. Limits (lean/LIMITS.md, L57): coreD, at any runK | runP, is a conditional on
  keySound, entrySound, proofSound, none of them proved here. dec: the frame's files alone read it.
Over TieAtValues.lean (see TAt.lean's head): every name takes `it` in
the place of pol | KL where these were handed on to the coding; pol, KL, lay stay for
the public reading. The same record with the parameter bytes a letter:
Johnson/Flat/Told/Dec/TAtBy.lean.
No soundness is claimed.
-/
import Johnson.Flat.Told.Dec.TAt

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
        ByteArray) (sR : ℕ)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP
                                    + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
        (saltG G) P) (d₀ : Dig 256)


/-- **THE VALUE, AT LETTERS.** -/
def toldD (e : D8) : LayoutsByPublicReading (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N
                                d₀ e)) :=
  toldFamD (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e)

section Sealed
/- Lean compares these three names and does not unfold them: unfolded, it does not come back from
    comparing the coding with itself (a timeout at whnf, in each build where it was tried). -/
attribute [local irreducible] mD PV.EncId.encF PV.MFull.cfgF

/-- **d ↦ tAt … d IS A FAMILY THAT PARTS FROM ONE MEMBER IN cfg, m, enc ALONE.** -/
theorem tD_fam (e d : D8) : tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ d = lettersFamD
    (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) d :=
  tAtR_with A E G (digToBytes d.1) DK DP runK runP dec P (digToBytes e.1) (mD A E G DK DP runK runP
      dec P h₀ it sR hDK hDP hK d)
    (mD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK e) N d₀ d.1
        (OnBytes.K.Arm.bytesToDig_digToBytes d.1)

/-- «code», at the family's letters. -/
theorem codeFamD (e : D8) : ZKCP.CodeIsOneToOne (famD A E G DK DP runK runP dec P h₀ it pol KL lay
    sR hDK hDP hK N d₀ e).encT :=
  PV.EncId.encF_oneToOne (restOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG
                            G).logLeaves G.early (saltG G) P)

end Sealed

/- From here on Lean compares the names tD and pub8 and does not unfold them. -/
attribute [local irreducible] tD pub8

/-- **THE RECORD's INPUT AT d IS THE FRAME's INPUT AT THE FAMILY's MEMBER AT d.** -/
theorem at_toldD (e d : D8) : (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N
    d₀ e).at d = innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ d) := by
  rw [tD_fam A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e d]
  exact at_toldFamD (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) d

theorem noCoinD (e : D8) : (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀
    e).Pub.NoCoin := famD_noCoin (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N
    d₀ e)

theorem asksD (e : D8) : (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀
    e).Pub.AsksIn fun _ s => (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀
    e).Pt s := famD_asks (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e)

theorem onceD (e : D8) : NoRepeat (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK
    N d₀ e).Pub := famD_once (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀
    e)

/-- **«spare».** -/
theorem spareD (e : D8) : ∀ d s, (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK
    N d₀ e).Pt s → IsOther ((toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀
    e).m d) s := fun d s hs =>
  mOneAt_isOther169 A E G (digToBytes d.1) (size_digToBytes d.1) DK DP runK runP dec P h₀ it sR
    (PV.RunArgsF.pdLOf (d.2.map digToBytes)) (PV.RunArgsF.pd3At (d.2.map digToBytes) 4)
        (PV.RunArgsF.pd3At (d.2.map digToBytes) 1)
    hDK hDP hK s hs

/-- **«word».** -/
theorem wordD (e : D8) : ∀ d d', (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK
    N d₀ e).part d = (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e).part
    d' →
    (extractorOverOneHashFunction ((toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e).m d)
        (indexExtractorAtRootAndOutOfDomainSample (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀
                                                  e)).queryLayout)).Ei =
      (extractorOverOneHashFunction ((toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e).m d')
          (indexExtractorAtRootAndOutOfDomainSample (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀
                                                    e)).queryLayout)).Ei := by
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
theorem codeD (e : D8) : ZKCP.CodeIsOneToOne (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR
    hDK hDP hK N d₀ e).encT := codeFamD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK
    N d₀ e

/-- Every pair (told part, key) has a code. -/
theorem totalD (e : D8) (key : Dig 256 × KeyRoot 256 (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec
                 P h₀ it sR hDK hDP hK N d₀ e)).protocol) : (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK
                        hDP hK N d₀ e).encT key ≠ none :=
  PV.EncId.encF_total (restOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG
                            G).logLeaves G.early (saltG G) P) key

set_option maxRecDepth 20000 in
/-- **THE FIFTEEN AT EVERY d**, from keySound, entrySound, proofSound at the member e's names. -/
theorem coreD (e : D8) (hk : kThree .two DK [] DP ≤ KF DK DP)
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
    (d : (toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e).D) :
    CompilerSoundnessConditions ((toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e).beside
                            (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).Wn
                          (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).Rno
                          (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).x₀
                          (soundnessAnalysisDataAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e)).εs d) :=
  core_toldFamD (famD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) (codeFamD
      A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e) hk bL wLk own dL wK dK wP
      dP kS eS pS d

/-- **«fits», at letters**: innerCompiledVerifier at the frame's input at the family's member at d IS innerCompiledVerifier
    at the record's input at d. -/
theorem fitsD (e d : D8) (commitment : Commitment) (prompt output : List Token)
    (proof : VerifierAndGoals.TypedProof (FsAtR A E G DK DP runK runP dec) P) :
    innerCompiledVerifier (innerCompilerInputAtFullSize (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ d))
        commitment prompt output proof =
      innerCompiledVerifier ((toldD A E G DK DP runK runP dec P h₀ it pol KL lay sR hDK hDP hK N d₀ e).at d)
          commitment prompt output proof :=
  congrArg (fun T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG
                                  G).logLeaves G.early (saltG G) (KF DK DP) P =>
    innerCompiledVerifier (innerCompilerInputAtFullSize T) commitment prompt output proof) (tD_fam A E G DK DP runK runP dec
                                 P h₀ it pol KL lay sR hDK hDP hK N d₀ e d)

end Sealed2

end Fam

end LPFD.Full

#print axioms LPFD.Full.toldD
#print axioms LPFD.Full.tD_fam
#print axioms LPFD.Full.at_toldD
#print axioms LPFD.Full.noCoinD
#print axioms LPFD.Full.asksD
#print axioms LPFD.Full.onceD
#print axioms LPFD.Full.spareD
#print axioms LPFD.Full.wordD
#print axioms LPFD.Full.codeD
#print axioms LPFD.Full.totalD
#print axioms LPFD.Full.coreD
#print axioms LPFD.Full.fitsD
#print axioms LPFD.Full.codeFamD
