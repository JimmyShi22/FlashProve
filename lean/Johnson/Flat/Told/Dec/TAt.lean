-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/Dec/TAt.lean: a twin, made by program, of Johnson/Flat/Told/TAt.lean
  over tAt over the D-names (Johnson/Top/Fire/Code/TieAtValues.lean: tAt ·
  tAtR · vAtR · mOneAt take the entry file's decision «dec» behind runP; ds xs are pinned at
  PV.EntryFive.dsF | xsF; the coding is PV.MFull.mFOneD) and the frame with the entry file's three
  letters (InnerCompilerInputAndAnalysisFieldsAtFullSize).
The declared names are the original's (LPFD.Full.tD · toldD · spareD …), as TieAtValues.lean's are.
  The original is not in this library. Where this twin parts: coreD has
  entrySound (eS) as a premise in the theorem on codes' place, hk at «[]», and the four tests on
  dsF's numbers. Who reads each letter, and the limits: the three paragraphs below. dec: the
  frame's files alone read it.
That head's three paragraphs on this, word for word, since that file is not in this tree (they are
  written of the original's statements, in its names):
  Who reads each letter. d.1: cfg (cfgF of its bytes), m (c), enc. d.2: m alone (pdL := the first;
    dP := the second to fourth; dK := the fifth to seventh; where the list is too short: empty
    bytes: PV.RunArgsF.pdLOf | pd3At). lay: famD's Pub alone. e: which member is T₀.
  ∃: IsCall169 s in a premise is opened; encId_hasCode's «∃ code» is opened to show ≠ none: nothing
    that a verifier reads is chosen.
  Does not show. That the verifier's queries pass mFOne's tests of fitness. That c, pdL, dK, dP are
    any hash's values. Nothing on soundness. No verifier is judged: every statement is general in
    runK | runP.
Over TieAtValues.lean (the request's item as a letter: `mOneAt` takes
it : XF → ByteArray in the place of pol | KL): `mD`, `tD`, `famD`, `mOneAt_isOther169`,
`mOneAt_word` take `it` likewise; `famD` keeps pol, KL, lay for the
public reading. "For all pol KL" is widened to "for all it".
No soundness is claimed.
-/
import Johnson.Flat.Told.FamilyD
import Johnson.Flat.Told.AnyLawsD
import Johnson.Top.Fire.Code.TieAtValues
import Ladder
import Johnson.TypedOracleCompiler.Top.IdSeedAt
import Johnson.TypedOracleCompiler.Top.IdSeedHasCode
import Johnson.TypedOracleCompiler.Top.TieIdBytes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace PV.EncId
open _root_.Iop (Dig InteractiveOracleProof twoExternalStrings)
open OnBytes OnBytes.Flat OnBytes.Slice OnBytes.Tie
open OnBytes.RunA (RestR LrG)
open _root_.Run.PQ (SgX)
open OnBytes.K OnBytes.K.IdTable OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch.Cms (KeyRoot)

/-- **«code» at PV.EncId.encF**: it is encId (encF_eq), which is one to one
    (encId_oneToOne). At every rest T. -/
theorem encF_oneToOne {I' X' RI : Type} [Fintype RI] [Nonempty RI] {a : ℕ}
    {Q : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ a) SgX)}
    (T : RestR I' X' RI (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE) a Q) :
    ZKCP.CodeIsOneToOne fun k : Dig 256 × KeyRoot 256 (LrG T) => encF k.1 k.2.cm k.2.rcd := by
  have e : encId recordGround T = fun k => encF k.1 k.2.cm k.2.rcd := funext (encF_eq T)
  have h := encId_oneToOne recordGround T
  rw [e] at h
  exact h

/-- **Every pair (told part, key) has a code under encF.** -/
theorem encF_total {I' X' RI : Type} [Fintype RI] [Nonempty RI] {a : ℕ}
    {Q : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ a) SgX)}
    (T : RestR I' X' RI (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE) a Q)
    (k : Dig 256 × KeyRoot 256 (LrG T)) : encF k.1 k.2.cm k.2.rcd ≠ none := by
  obtain ⟨code, h⟩ := encId_hasCode recordGround T room_recordGround k
  rw [← encF_eq T k, h]
  exact Option.some_ne_none _

end PV.EncId

namespace LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open OnBytes.Maker.Page (Pd3 kindsAndWorkBelow256)
open OnBytes.K.Arm.Pub
open PV.EntryFive (dsF xsF)

section One
variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c :
                ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull →
        PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL
        : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP
                                    + 1 + 1 < 2 ^ 49)

/-- **«spare» at the run's coding.** -/
theorem mOneAt_isOther169 (s : List Bool) (hs : OnBytes.Slice.IsCall169 s) :
    ((mOneAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK).dec s).1 =
        TypedOracleCompiler.Compile.Batch.OracleName.other := by
  unfold mOneAt PV.MFull.mFOneD
  exact W4M.mAny_isOther169 (s := s) (hs := hs) ..

/-- **«word» at the run's coding**: one c; the seven further digests may part. -/
theorem mOneAt_word (pdL' : Dig 256) (dK' dP' : Pd3)
    (T₀ : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
        (saltG G) (KF DK DP) P) :
    (extractorOverOneHashFunction (mOneAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK) (indexExtractorAtRootAndOutOfDomainSample
                              T₀.W)).Ei =
      (extractorOverOneHashFunction (mOneAt A E G c hc DK DP runK runP dec P h₀ it sR pdL' dK' dP' hDK hDP hK)
          (indexExtractorAtRootAndOutOfDomainSample T₀.W)).Ei := by
  unfold mOneAt PV.MFull.mFOneD
  exact word_mAnyAtD T₀ ..

variable (c₀ : ByteArray) (m m₀ : OracleCoding (typedOracleFamily 256 (KF DK DP + 1) (CsAtR A E G DK DP runK runP dec
                         P)) 256)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
        (saltG G) P) (d₀ : Dig 256)

/-- lettersAtFullD passes three fields of the verifier's side on: at a letter V. -/
theorem lettersAtFullD_with (V : VerifierSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2
    (sBG G).logLeaves G.early (saltG G) (KF DK DP) P)
    (cfg : List (Dig 256)) (enc : KeyRoot 256 ((FsAtR A E G DK DP runK runP dec).withProvers P) → Option
        ZKCP.Str) :
    lettersAtFullD { V with cfg := cfg, m := m, enc := enc } N d₀ =
      { lettersAtFullD V N d₀ with cfg := cfg, m := m, enc := enc } := rfl

/-- The verifier's side at (c, m) is the verifier's side at (c₀, m₀) with three fields laid anew.
    -/
theorem vAtR_with : vAtR A E G c DK DP runK runP dec P m =
    { vAtR A E G c₀ DK DP runK runP dec P m₀ with
      cfg := PV.MFull.cfgF c, m := m, enc := fun k => PV.EncId.encF (bytesToDig c) k.cm k.rcd } :=
          rfl

/-- **T at (c, m) is T at (c₀, m₀) with three fields laid anew**: at letters m m₀. x: the
    digest of c's bytes. -/
theorem tAtR_with (x : Dig 256) (hx : bytesToDig c = x) :
    tAtR A E G c DK DP runK runP dec P m N d₀ =
      { tAtR A E G c₀ DK DP runK runP dec P m₀ N d₀ with
        cfg := PV.MFull.cfgF c, m := m, enc := fun k => PV.EncId.encF x k.cm k.rcd } := by
  subst hx
  exact (congrArg (fun V => lettersAtFullD V N d₀) (vAtR_with A E G c DK DP runK runP dec P c₀ m
      m₀)).trans
    (lettersAtFullD_with A E G DK DP runK runP dec P m N d₀ _ _ _)

end One

/-! ## The family over the public reading's values, AT LETTERS (G among them) -/

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

/-- The run's coding at d. -/
def mD (d : D8) : OracleCoding (typedOracleFamily 256 (KF DK DP + 1) (CsAtR A E G DK DP runK runP dec P)) 256 :=
  mOneAt A E G (digToBytes d.1) (size_digToBytes d.1) DK DP runK runP dec P h₀ it sR
    (PV.RunArgsF.pdLOf (d.2.map digToBytes)) (PV.RunArgsF.pd3At (d.2.map digToBytes) 4)
        (PV.RunArgsF.pd3At (d.2.map digToBytes) 1) hDK hDP hK

/-- **THE FAMILY d ↦ tAt … d**: T at the bytes of the eight digests. -/
def tD (d : D8) : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves
    G.early (saltG G) (KF DK DP) P :=
  tAtR A E G (digToBytes d.1) DK DP runK runP dec P (mD A E G DK DP runK runP dec P h₀ it sR hDK
      hDP hK d) N d₀

/-- The family's letters over T₀ := tD … e. -/
def famD (e : D8) : FamLettersD (tD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK N d₀ e) where
  pol := pol
  KL := KL
  lay := lay
  cfgOf := fun d => PV.MFull.cfgF (digToBytes d.1)
  mOf := mD A E G DK DP runK runP dec P h₀ it sR hDK hDP hK
  encT := fun k => PV.EncId.encF k.1 k.2.cm k.2.rcd
  d₀ := d₀

end Fam

end LPFD.Full

#print axioms PV.EncId.encF_oneToOne
#print axioms PV.EncId.encF_total
#print axioms LPFD.Full.mOneAt_isOther169
#print axioms LPFD.Full.mOneAt_word
#print axioms LPFD.Full.tAtR_with
#print axioms LPFD.Full.famD
#print axioms LPFD.Full.lettersAtFullD_with
#print axioms LPFD.Full.vAtR_with
