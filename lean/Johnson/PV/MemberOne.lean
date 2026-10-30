-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MemberOne.lean: a member of the premises of `mAll` (Johnson/PV/CutAll.lean): both files'
  laws at one page, at the carrier of any object with records, general in both files' rounds' data
  DK, DP and at any digests dK, dP.

The page is `pageD` of Johnson/Top/ProofPageD.lean, whose field for the key file's data is a letter
  there: here it is laid by the same `fillJ`, at `silentKey`. Every law is a call of a law of the
  library.
Premises that stay: both read-backs are one to one where they read (hrdK, hrdP); `kindsAndWorkBelow256` of both
  data; K + 2 < 2 ^ 49; cfg has 32 bytes; the laws that S : FrontSet brings; the entry file's code's
  label is none of the six.
Letters: all else, `back` among them.
Limits: cfg, dK, dP are letters: nothing here says that they are any hash's. That a verifier's
  queries pass the tests of fitness is not shown. Nothing on soundness.

-/
import Johnson.PV.CutAll
import Johnson.Top.ProofPageD
import OnBytes.K.Arm.KeyCoding

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofFront

open _root_.Run _root_.Run.PQ Iop Rom
open OnBytes.Maker OnBytes.Maker.Page
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open _root_.Compile.Joined (JoinMsg)
open OnBytes.K.Arm (KeyLaws ProofLaws digBytes takenCalls_of BothCut BothLaws LinkLaws IsLab mAll
  cutAll LabelsApart)
open OnBytes.K.Arm.KeyGlue (keyCutOf)
open OnBytes.K.Arm.ProofGlue (proofCutOf)
open OnBytes.K.Arm.FileInj (FitJ LawsJ)

variable {I X : Type} {L : HolographicProtocol I X} (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
  {K : ℕ} (C : CK) (DK DP : WholeD)
  (tFk : FrontMsg (List E)) (tJk : JoinMsg (List E) ByteArray) (t3k : ByteArray)
  (tFp : FrontMsg (List E)) (tJp : JoinMsg (List E) ByteArray) (t3p : ByteArray)
  (rdK : PBt (typedOracleCarrier L Bd aT aL) .test →
    Option (PlainPart (chainsOf C DK tFk tJk t3k).sh (chainsOf C DK tFk tJk t3k).ann))
  (rdP : PBt (typedOracleCarrier L Bd aT aL) .onl →
    Option (PlainPart (chainsOf C DP tFp tJp t3p).sh (chainsOf C DP tFp tJp t3p).ann))
  (h₀ : HId) (k : Params.KeyChains) (c : Params.ProofChains)
  {sp : X → ByteArray × ByteArray} {r₀ : L.Rec} (S : FrontSet L sp r₀)
  (tlK tlP : Dig 256 → List E → List (Dig 256))
  (cfg : ByteArray) (sR : ℕ)
  (bd : (typedOracleCarrier L Bd aT aL).Bd → List Bool) (p0 p1 : PBt (typedOracleCarrier L Bd aT aL) .test)
  (isP0 isP1 : PBt (typedOracleCarrier L Bd aT aL) .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (Lk : LinkCode (typedOracleCarrier L Bd aT aL) (K + 1)) (V : Leaves (typedOracleCarrier L Bd aT aL))
  (dK dP : Pd3)

/-- The key file's data, laid as the proof file's are. -/
def keyJOne : FileJ (typedOracleCarrier L Bd aT aL) .test :=
  fillJ C DK tFk tJk t3k rdK (silentKey h₀ k _)

/-- The test on the key file's chain queries. -/
def fitKOne : FitJ (typedOracleCarrier L Bd aT aL) .test :=
  fitAt C DK tFk tJk t3k rdK (fFrontK tlK) (fJoin tlK) fSeam

/-- **ONE PAGE**, with both files' data laid and the six digests as data. -/
def pageOne : PageJ (typedOracleCarrier L Bd aT aL) (K + 1) :=
  pageD Bd aT aL C DP tFp tJp t3p rdP h₀ c cfg sR (keyJOne Bd aT aL C DK tFk tJk t3k rdK h₀ k) bd
    p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V sp dK dP

/-- **The key file's laws at that page.** -/
theorem keyLaws_one (hrdK : ∀ z z' w, rdK z = some w → rdK z' = some w → z = z')
    (hDK : kindsAndWorkBelow256 DK = true) (hK : K + 1 + 1 < 2 ^ 49) (hc : cfg.size = digBytes) :
    KeyLaws (keyCutOf
      (pageOne (sp := sp) Bd aT aL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c cfg sR bd p0 p1
        isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP)
      (fitKOne Bd aT aL C DK tFk tJk t3k rdK tlK)) :=
  keyLaws_withPd _ _
    (laws_fill C DK tFk tJk t3k rdK (silentKey h₀ k _) hrdK (silentKey_laws h₀ k tlK) hDK (K + 1)
        hK)
    (takenCalls_of _ V rfl p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest rfl) hc
    (by show Params.labelOneTime ≠ Fmt.recordLabel; decide)
    (by show Params.labelShared ≠ Fmt.recordLabel; decide)
    (by show Params.labelSecond ≠ Fmt.recordLabel; decide) dK dP

/-- The data of the one cut. -/
def bothOne : BothCut (typedOracleCarrier L Bd aT aL) (K + 1) :=
  let P := pageOne (sp := sp) Bd aT aL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c cfg sR bd p0
    p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP
  ⟨P, (keyCutOf P (fitKOne Bd aT aL C DK tFk tJk t3k rdK tlK)).fitFb,
    (keyCutOf P (fitKOne Bd aT aL C DK tFk tJk t3k rdK tlK)).fitG,
    (proofCutOf P (fitFill Bd aT aL C DP tFp tJp t3p rdP S tlP)).fitFb,
    (proofCutOf P (fitFill Bd aT aL C DP tFp tJp t3p rdP S tlP)).fitG⟩

/-- **BOTH FILES' LAWS AND THE LABELS, AT ONE PAGE.** -/
theorem bothLaws_one (hrdK : ∀ z z' w, rdK z = some w → rdK z' = some w → z = z')
    (hrdP : ∀ z z' w, rdP z = some w → rdP z' = some w → z = z')
    (hDK : kindsAndWorkBelow256 DK = true) (hDP : kindsAndWorkBelow256 DP = true) (hK : K + 1 + 1 < 2 ^ 49)
    (hc : cfg.size = digBytes) :
    BothLaws (bothOne Bd aT aL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c S tlK tlP cfg sR bd p0
        p1
      isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) where
  key := keyLaws_one Bd aT aL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c tlK cfg sR bd p0 p1
    isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP hrdK hDK hK hc
  proof := proofLaws_pageD Bd aT aL C DP tFp tJp t3p rdP h₀ c S tlP cfg sR _ bd p0 p1 isP0 isP1 cfgL
    sh hp0 hp1 rest Lk V hrdP hDP hK hc dK dP
  apart := fun l hk hp => by
    have hk' : l = Params.labelOneTime ∨ l = Params.labelShared ∨ l = Params.labelSecond := hk
    have hp' : l = Params.labelFirst ∨ l = Params.labelSharedProof ∨
      l = Params.labelSecondProof := hp
    rcases hk' with rfl | rfl | rfl <;> rcases hp' with e | e | e <;> exact absurd e (by decide)

/-- **The entry file's spelling's laws at that page**, if its label is none of the six. -/
theorem linkLaws_one
    (hL : Lk.l ∉ [Params.labelOneTime, Params.labelShared, Params.labelSecond, Params.labelFirst,
      Params.labelSharedProof, Params.labelSecondProof]) :
    LinkLaws (bothOne Bd aT aL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c S tlK tlP cfg sR bd p0
        p1
      isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) Lk.l where
  inj := fun _ _ _ a b => Lk.pL.inj a b
  is := fun x s a => Lk.his x s a
  lt := Lk.hlt
  neS := Lk.hne
  ne := fun l hl e => by
    have hl' : (l = Params.labelOneTime ∨ l = Params.labelShared ∨ l = Params.labelSecond) ∨
      (l = Params.labelFirst ∨ l = Params.labelSharedProof ∨ l = Params.labelSecondProof) := hl
    apply hL
    rw [← e]
    rcases hl' with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> simp

/-- **THE ONE ENCODING OF ALL THREE FILES' TYPED QUERIES, AT THE CARRIER OF ANY OBJECT WITH RECORDS,
AT ANY ROUNDS' DATA AND ANY DIGESTS.** -/
noncomputable def mOne (hrdK : ∀ z z' w, rdK z = some w → rdK z' = some w → z = z')
    (hrdP : ∀ z z' w, rdP z = some w → rdP z' = some w → z = z')
    (hDK : kindsAndWorkBelow256 DK = true) (hDP : kindsAndWorkBelow256 DP = true) (hK : K + 1 + 1 < 2 ^ 49)
    (hc : cfg.size = digBytes)
    (hL : Lk.l ∉ [Params.labelOneTime, Params.labelShared, Params.labelSecond, Params.labelFirst,
      Params.labelSharedProof, Params.labelSecondProof])
    (back : StrCode (AllPts 256 (K + 1) (typedOracleCarrier L Bd aT aL))) :
    OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier L Bd aT aL)) 256 :=
  mAll
    (bothLaws_one Bd aT aL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c S tlK tlP cfg sR bd p0 p1
        isP0
      isP1 cfgL sh hp0 hp1 rest Lk V dK dP hrdK hrdP hDK hDP hK hc)
    (linkLaws_one Bd aT aL C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c S tlK tlP cfg sR bd p0 p1
        isP0
      isP1 cfgL sh hp0 hp1 rest Lk V dK dP hL) back

end OnBytes.K.Arm.ProofFront

#print axioms OnBytes.K.Arm.ProofFront.keyLaws_one
#print axioms OnBytes.K.Arm.ProofFront.bothLaws_one
#print axioms OnBytes.K.Arm.ProofFront.linkLaws_one
#print axioms OnBytes.K.Arm.ProofFront.mOne
example : OnBytes.Params.labelLink ∉ [OnBytes.Params.labelOneTime, OnBytes.Params.labelShared,
    OnBytes.Params.labelSecond, OnBytes.Params.labelFirst, OnBytes.Params.labelSharedProof,
    OnBytes.Params.labelSecondProof] := by decide
