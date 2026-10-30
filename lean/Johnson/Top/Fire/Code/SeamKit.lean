-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/SeamKit.lean: THE LETTER h₀ IS IDLE IN THE ONE CODING OF ALL THREE FILES' TYPED QUERIES, at any interface and
any letters: for Seam.lean.
  `mAll_congr`: the coding `OnBytes.K.Arm.mAll` (Johnson/PV/CutAll.lean) is a function of the data of the cut
    alone: its two further arguments are proofs.
  `pageAny_idle`, `bothAny_idle`: the page of all three files and the data of the one cut (`W4M.pageAny`, `W4M.bothAny`,
    Johnson/PV/MvAny.lean) are the same at any two h₀, h₁: h₀ is read for the six digests of the chains' parameter bytes alone
    (`silentKey`, `silentProof`, OnBytes/Maker/Page/Silent.lean), and the page lays dK, dP over just these (`PageJ.withPd`): by
    unfolding, at letters.
  `mAny_idle`: so is the coding `W4M.mAny` (Johnson/PV/LawsAny.lean).
Why at letters: asked at a size's own values Lean unfolds these values (small: three minutes; full: out of memory at 64 GiB).
Limits: equations between terms. k and c (the chains' parameters) are idle likewise, by reading: not stated. Nothing on soundness.

-/
import Johnson.PV.LawsAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open _root_.Iop hiding BatchProtocol

/-- The coding is a function of the data of the cut alone. -/
theorem mAll_congr {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} {C C' : BothCut L K} (e : C = C') (H : BothLaws C) {lL : ℕ}
    (G : LinkLaws C lL) (H' : BothLaws C') (G' : LinkLaws C' lL) (back : StrCode (AllPts 256 K L)) :
    mAll H G back = mAll H' G' back := by
  subst e
  rfl

end OnBytes.K.Arm

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Run.PageRun
open OnBytes OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.K.Arm.ProofFront OnBytes.Maker OnBytes.Maker.Page Johnson.RunOne
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
  (h₀ h₁ : HId) (k : OnBytes.Params.KeyChains) (c : OnBytes.Params.ProofChains)
  (req : X → ByteArray × ByteArray) (okX : X → Bool)
  (tlK tlP : Dig 256 → List OnBytes.E → List (Dig 256))
  (cfg : ByteArray) (sR : ℕ) (bd : L.Bd → List Bool) (p0 p1 : PBt L .test)
  (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (Lk : LinkCode L (K + 1)) (V : Leaves L) (dK dP : Pd3)

/-- The page of all three files reads h₀ for what dK, dP overwrite alone. -/
theorem pageAny_idle :
    pageAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP =
      pageAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₁ k c req cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP := rfl

/-- So do the data of the one cut. -/
theorem bothAny_idle :
    bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP = bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₁ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP := by
  unfold bothAny
  rw [pageAny_idle C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ h₁]

variable (hrdK : ∀ z z' w, rdK z = some w → rdK z' = some w → z = z')
  (hrdP : ∀ z z' w, rdP z = some w → rdP z' = some w → z = z')
  (hDK : kindsAndWorkBelow256 DK = true) (hDP : kindsAndWorkBelow256 DP = true) (hK : K + 1 + 1 < 2 ^ 49)
  (hc : cfg.size = digBytes)
  (hreq : ∀ x y, okX x = true → okX y = true → req x = req y → x = y)
  (hL : Lk.l ∉ [Params.labelOneTime, Params.labelShared, Params.labelSecond, Params.labelFirst,
    Params.labelSharedProof, Params.labelSecondProof])
  (back : StrCode (AllPts 256 (K + 1) L))

/-- **The letter h₀ is idle in the one coding.** -/
theorem mAny_idle :
    mAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP hrdK hrdP hDK hDP hK hc hreq hL back =
      mAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₁ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP hrdK hrdP hDK hDP hK hc hreq hL back :=
  mAll_congr (bothAny_idle C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ h₁ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP) _ _ _ _ back

end W4M

#print axioms OnBytes.K.Arm.mAll_congr
#print axioms W4M.pageAny_idle
#print axioms W4M.bothAny_idle
#print axioms W4M.mAny_idle
