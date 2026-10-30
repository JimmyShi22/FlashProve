-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Told/AnyLaws.lean: two of the premises that the told theorem adds
(`innerCompiledVerifier_sound_byPublicReading`, Johnson/Top/InnerCompiledVerifierByPublicReading.lean), "spare" and "word", at the coding of
queries `W4M.mAny` (Johnson/PV/LawsAny.lean). Statements and proofs.

Why. The told theorem asks of the coding m d of typed queries, at every value d of the public
reading: (spare) every public string codes a point of the spare oracle; (word) what the extractor
reads off a log depends on d through the told part alone. The coding that a real run uses is an
instance of `mAny`.

Main names.
  `W4M.bothAny_cfg`, `W4M.bothAny_leafX`: the page's configuration digest is the letter cfg; its
    spelling of leaves reads neither the entry file's code nor the six digests. Both by definition.
  `W4M.mAny_isOther169`: spare. The string of a call with the number 169 codes a point of the spare
    oracle, at every interface L.
  `VerifiableInference.OnPublicFiles.word_mAnyAt`: word, at the carrier and the wiring of the full-size
    frame (Johnson/Flat/TwoSizesAt.lean). Two codings that differ in the entry file's code Lk and in
    the six digests dK, dP alone give one reading of every log.

How. `mAny` unfolds to `mAll` (Johnson/PV/CutAll.lean): spare is `mAll_call` with `mAll_isOther`;
word is `word_mAll` (Johnson/PV/WordAll.lean).

Limits. Nothing on whether a verifier's queries pass the coding's own tests of fitness. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.PV.LawsAny
import Johnson.PV.WordAll
import Johnson.Flat.TwoSizesAt
import OnBytes.Slice.WalkOff

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Run.PageRun
open OnBytes OnBytes.K.Arm OnBytes.K.Arm.FileInj OnBytes.K.Arm.ProofFront OnBytes.Maker OnBytes.Maker.Page Johnson.RunOne
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open _root_.Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (HId)

section Any
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
  (Lk Lk' : LinkCode L (K + 1)) (V : Leaves L) (dK dP dK' dP' : Pd3)

/-- The page's configuration's digest is the letter cfg. -/
theorem bothAny_cfg : (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP).P.cfg = cfg := rfl

/-- The page's spelling of leaves reads neither the entry file's code nor the six digests. -/
theorem bothAny_leafX : (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP).P.leafX =
    (bothAny (K := K) C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk' V dK' dP').P.leafX := rfl

variable (hrdK : ∀ z z' w, rdK z = some w → rdK z' = some w → z = z')
  (hrdP : ∀ z z' w, rdP z = some w → rdP z' = some w → z = z')
  (hDK : kindsAndWorkBelow256 DK = true) (hDP : kindsAndWorkBelow256 DP = true) (hK : K + 1 + 1 < 2 ^ 49)
  (hc : cfg.size = digBytes)
  (hreq : ∀ x y, okX x = true → okX y = true → req x = req y → x = y)
  (hL : Lk.l ∉ [Params.labelOneTime, Params.labelShared, Params.labelSecond, Params.labelFirst,
    Params.labelSharedProof, Params.labelSecondProof])
  (back : StrCode (AllPts 256 (K + 1) L))

/-- Spare: the string of a call with the number 169 codes a point of the spare oracle. -/
theorem mAny_isOther169 (s : List Bool) (hs : OnBytes.Slice.IsCall169 s) :
    ((mAny C DK DP tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V dK dP hrdK hrdP hDK hDP hK hc hreq hL back).dec s).1 = TypedOracleCompiler.Compile.Batch.OracleName.other := by
  obtain ⟨half, t, i, st, bs, hh, hst, rfl⟩ := hs
  unfold mAny
  exact mAll_isOther _ _ _ _ (mAll_call _ _ _ 169 (by decide) half hh t i st bs hst 0)

end Any

end W4M

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.ProofFront OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.K.Arm.FileInj Johnson.RunOne
open TypedOracleCompiler.Run TypedOracleCompiler.Run.PageRun
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open _root_.Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK)

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ} {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}
  (T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P)

set_option quotPrecheck false in
/-- The interface of the typed oracles over the three files. -/
local notation "Cf" => typedOracleCarrier ((threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).withProvers P) (List Bool) (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).annT (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).annL

/-- Word, at the frame's carrier and wiring: two codings that differ in the entry file's code and the
six digests alone give one reading of every log. -/
theorem word_mAnyAt (C : CK) (DKa DPa : WholeD)
    (tFk : FrontMsg (List OnBytes.E)) (tJk : JoinMsg (List OnBytes.E) ByteArray) (t3k : ByteArray)
    (tFp : FrontMsg (List OnBytes.E)) (tJp : JoinMsg (List OnBytes.E) ByteArray) (t3p : ByteArray)
    (rdK : PBt (Cf) .test → Option (PlainPart (chainsOf C DKa tFk tJk t3k).sh (chainsOf C DKa tFk tJk t3k).ann))
    (rdP : PBt (Cf) .onl → Option (PlainPart (chainsOf C DPa tFp tJp t3p).sh (chainsOf C DPa tFp tJp t3p).ann))
    (h₀ : HId) (k : OnBytes.Params.KeyChains) (c : OnBytes.Params.ProofChains)
    (req : _ → ByteArray × ByteArray) (okX : _ → Bool)
    (tlK tlP : Dig 256 → List OnBytes.E → List (Dig 256))
    (cfg : ByteArray) (sR : ℕ) (bd : (Cf).Bd → List Bool) (p0 p1 : PBt (Cf) .test)
    (isP0 isP1 : PBt (Cf) .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
    (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
    (Lk Lk' : LinkCode (Cf) (K + 1)) (V : Leaves (Cf)) (dK dP dK' dP' : Pd3)
    (hrdK : ∀ z z' w, rdK z = some w → rdK z' = some w → z = z')
    (hrdP : ∀ z z' w, rdP z = some w → rdP z' = some w → z = z')
    (hDK : kindsAndWorkBelow256 DKa = true) (hDP : kindsAndWorkBelow256 DPa = true) (hK : K + 1 + 1 < 2 ^ 49)
    (hc : cfg.size = digBytes)
    (hreq : ∀ x y, okX x = true → okX y = true → req x = req y → x = y)
    (hL : Lk.l ∉ [OnBytes.Params.labelOneTime, OnBytes.Params.labelShared, OnBytes.Params.labelSecond, OnBytes.Params.labelFirst,
      OnBytes.Params.labelSharedProof, OnBytes.Params.labelSecondProof])
    (hL' : Lk'.l ∉ [OnBytes.Params.labelOneTime, OnBytes.Params.labelShared, OnBytes.Params.labelSecond, OnBytes.Params.labelFirst,
      OnBytes.Params.labelSharedProof, OnBytes.Params.labelSecondProof])
    (back : StrCode (AllPts 256 (K + 1) (Cf))) :
    (extractorOverOneHashFunction (W4M.mAny (L := Cf) (K := K) C DKa DPa tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
                              Lk V dK dP hrdK hrdP hDK hDP hK hc hreq hL back) (indexExtractorAtRootAndOutOfDomainSample T₀.W)).Ei =
      (extractorOverOneHashFunction (W4M.mAny (L := Cf) (K := K) C DKa DPa tFk tJk t3k tFp tJp t3p rdK rdP h₀ k c req okX tlK tlP cfg sR bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
                              Lk' V dK' dP' hrdK hrdP hDK hDP hK hc hreq hL' back) (indexExtractorAtRootAndOutOfDomainSample T₀.W)).Ei := by
  unfold W4M.mAny
  exact word_mAll T₀.W _ _ _ _ back rfl rfl

end VerifiableInference.OnPublicFiles

#print axioms W4M.bothAny_cfg
#print axioms W4M.bothAny_leafX
#print axioms W4M.mAny_isOther169
#print axioms VerifiableInference.OnPublicFiles.word_mAnyAt
