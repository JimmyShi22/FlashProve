-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/LawsAny.lean: **THE ONE CODING IS ONE TO ONE AND ONTO AT ANY INTERFACE**: the premises of
  mAll (Johnson/PV/CutAll.lean) PROVED at W4M.bothAny (Johnson/PV/MvAny.lean), general in the
  interface L : BatchProtocolWithLeafBody I X: so also at carrierV of the one sheet's own letters: no object with
records, no honest side is named. MemberOne.lean (this folder)
  has them at typedOracleCarrier of an object with records, through S : FrontSet; every law of
  the library beneath is general in L: here they are called so.
PREMISES THAT STAY: both read-backs are one to one where they read (hrdK, hrdP: at «some»: trivial)
  · kindsAndWorkBelow256 of both data · K + 2 < 2 ^ 49 · cfg has 32 bytes · **hreq: on what passes okX the
  request's two strings are one to one** · the entry file's code's label is none of the six.
  keyLaws_any · proofLaws_any · bothLaws_any · linkLaws_any · **mAny … back : OracleCoding (typedOracleFamily 256 (K + 1)
    L) 256** (bijective by its type) · **mAny_blocks | mAny_rng := rfl · mAny_code**: at every
    oracle but the spare one its string IS mVOf (bothAny …) back.put's.
Nothing on soundness.


-/
import Johnson.PV.MvAny
import OnBytes.K.Arm.KeyCoding

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
    TypedOracleCompiler.Run.PageRun
open OnBytes OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.K.Arm.ProofFront OnBytes.Maker
    OnBytes.Maker.Page Johnson.RunOne
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open OnBytes.K.Arm.KeyGlue (keyCutOf)
open OnBytes.K.Arm.ProofGlue (proofCutOf)
open _root_.Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (HId)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}
  (C : CK) (DK DP : WholeD)
  (tFk : FrontMsg (List OnBytes.E)) (tJk : JoinMsg (List OnBytes.E) ByteArray) (t3k : ByteArray)
  (tFp : FrontMsg (List OnBytes.E)) (tJp : JoinMsg (List OnBytes.E) ByteArray) (t3p : ByteArray)
  (rdK : PBt L .test → Option (PlainPart (chainsOf C DK tFk tJk t3k).sh (chainsOf C DK tFk tJk t3k).ann))
  (rdP : PBt L .onl → Option (PlainPart (chainsOf C DP tFp tJp t3p).sh (chainsOf C DP tFp tJp t3p).ann))
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c : OnBytes.Params.ProofChains)
  (req : X → ByteArray × ByteArray) (okX : X → Bool)
  (tlK tlP : Dig 256 → List OnBytes.E → List (Dig 256))
  (cfg : ByteArray) (sR : ℕ) (bd : L.Bd → List Bool) (p0 p1 : PBt L .test)
  (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (Lk : LinkCode L (K + 1)) (V : Leaves L) (dK dP : Pd3)

/-- The key file's laws at the page. -/
theorem keyLaws_any (hrdK : ∀ z z' w, rdK z = some w → rdK z' = some w → z = z')
    (hDK : kindsAndWorkBelow256 DK = true) (hK : K + 1 + 1 < 2 ^ 49) (hc : cfg.size = digBytes) :
    KeyLaws (keyCutOf (pageAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req cfg sR bd
        p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) (fitKAny C DK tFk tJk t3k rdK tlK)) :=
  keyLaws_withPd _ _
    (laws_fill C DK tFk tJk t3k rdK (silentKey h₀ k _) hrdK (silentKey_laws h₀ k tlK) hDK (K + 1)
        hK)
    (takenCalls_of _ V rfl p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest rfl) hc
    (by show Params.labelOneTime ≠ Fmt.recordLabel; decide)
    (by show Params.labelShared ≠ Fmt.recordLabel; decide)
    (by show Params.labelSecond ≠ Fmt.recordLabel; decide) dK dP

/-- The proof file's laws at the page. -/
theorem proofLaws_any (hrdP : ∀ z z' w, rdP z = some w → rdP z' = some w → z = z')
    (hDP : kindsAndWorkBelow256 DP = true) (hK : K + 1 + 1 < 2 ^ 49) (hc : cfg.size = digBytes)
    (hreq : ∀ x y, okX x = true → okX y = true → req x = req y → x = y) :
    ProofLaws (proofCutOf (pageAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req cfg
        sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) (fitPAny C DP tFp tJp t3p rdP req okX
        tlP)) :=
  proofLaws_withPd _ _
    (laws_fill C DP tFp tJp t3p rdP (silentProof h₀ c req) hrdP (silentProof_laws h₀ c req okX hreq
        tlP) hDP (K + 1) hK)
    (taken_pageFill cfg sR _ _ bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V _) hc
    (by show Params.labelFirst ≠ Fmt.recordLabel; decide)
    (by show Params.labelSharedProof ≠ Fmt.recordLabel; decide)
    (by show Params.labelSecondProof ≠ Fmt.recordLabel; decide) dK dP

/-- **BOTH FILES' LAWS AND THE LABELS, AT ONE PAGE, AT ANY INTERFACE.** -/
theorem bothLaws_any (hrdK : ∀ z z' w, rdK z = some w → rdK z' = some w → z = z')
    (hrdP : ∀ z z' w, rdP z = some w → rdP z' = some w → z = z')
    (hDK : kindsAndWorkBelow256 DK = true) (hDP : kindsAndWorkBelow256 DP = true) (hK : K + 1 + 1 < 2 ^ 49)
    (hc : cfg.size = digBytes)
    (hreq : ∀ x y, okX x = true → okX y = true → req x = req y → x = y) :
    BothLaws (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR
        bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) where
  key := keyLaws_any C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req tlK cfg sR bd p0 p1 isP0
      isP1 cfgL sh hp0 hp1 rest Lk V dK dP hrdK hDK hK hc
  proof := proofLaws_any C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlP cfg sR bd p0 p1
      isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP hrdP hDP hK hc hreq
  apart := fun l hk hp => by
    have hk' : l = Params.labelOneTime ∨ l = Params.labelShared ∨ l = Params.labelSecond := hk
    have hp' : l = Params.labelFirst ∨ l = Params.labelSharedProof ∨
      l = Params.labelSecondProof := hp
    rcases hk' with rfl | rfl | rfl <;> rcases hp' with e | e | e <;> exact absurd e (by decide)

/-- The entry file's spelling's laws at that page, if its label is none of the six. -/
theorem linkLaws_any
    (hL : Lk.l ∉ [Params.labelOneTime, Params.labelShared, Params.labelSecond, Params.labelFirst,
      Params.labelSharedProof, Params.labelSecondProof]) :
    LinkLaws (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR
        bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) Lk.l where
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

section M
variable (hrdK : ∀ z z' w, rdK z = some w → rdK z' = some w → z = z')
  (hrdP : ∀ z z' w, rdP z = some w → rdP z' = some w → z = z')
  (hDK : kindsAndWorkBelow256 DK = true) (hDP : kindsAndWorkBelow256 DP = true) (hK : K + 1 + 1 < 2 ^ 49)
  (hc : cfg.size = digBytes)
  (hreq : ∀ x y, okX x = true → okX y = true → req x = req y → x = y)
  (hL : Lk.l ∉ [Params.labelOneTime, Params.labelShared, Params.labelSecond, Params.labelFirst,
    Params.labelSharedProof, Params.labelSecondProof])
  (back : StrCode (AllPts 256 (K + 1) L))

/-- **THE ONE ENCODING OF ALL THREE FILES' TYPED QUERIES, ONE TO ONE AND ONTO, AT ANY INTERFACE.**
  -/
noncomputable def mAny : OracleCoding (typedOracleFamily 256 (K + 1) L) 256 :=
  mAll (bothLaws_any C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1
      isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP hrdK hrdP hDK hDP hK hc hreq) (linkLaws_any C DK DP
      tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0
      hp1 rest Lk V dK dP hL) back

theorem mAny_blocks :
    (mVOf (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd
        p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) back.put).blocks =
      (mAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1
          cfgL sh hp0 hp1 rest Lk V dK dP hrdK hrdP hDK hDP hK hc hreq hL back).blocks := rfl

theorem mAny_rng :
    (mVOf (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd
        p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) back.put).rng =
      (mAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1
          cfgL sh hp0 hp1 rest Lk V dK dP hrdK hrdP hDK hDP hK hc hreq hL back).rng := rfl

/-- **AT EVERY ORACLE BUT THE SPARE ONE THE WRITING SIDE's STRING IS THE BIJECTIVE CODING's.** -/
theorem mAny_code (o : TypedOracleCompiler.Compile.Batch.OracleName) (ho : o ≠ .other) (q : domOf 256 L o) (j : Fin
                    (blk (K + 1) o)) :
    (mVOf (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd
        p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) back.put).code o q j =
      (mAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1
          cfgL sh hp0 hp1 rest Lk V dK dP hrdK hrdP hDK hDP hK hc hreq hL back).code o q j :=
  mVOf_code _ _ back o ho q j

end M

end W4M

#print axioms W4M.bothLaws_any
#print axioms W4M.linkLaws_any
#print axioms W4M.mAny
#print axioms W4M.mAny_code
