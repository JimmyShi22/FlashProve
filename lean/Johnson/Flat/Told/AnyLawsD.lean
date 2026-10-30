-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/AnyLawsD.lean: the premise "word" of the told theorem (`innerCompiledVerifier_sound_byPublicReading`,
Johnson/Top/InnerCompiledVerifierByPublicReading.lean) at the coding of queries `W4M.mAny` (Johnson/PV/LawsAny.lean), at the
carrier and the wiring of the full-size frame in which the entry file's rounds, openings and decision
are parameters (`InnerCompilerInputAndAnalysisFieldsAtFullSize`, Johnson/Flat/Dec/TwoSizesAt.lean). One statement with its proof.

`word_mAnyAtD` is `word_mAnyAt` (Johnson/Flat/Told/AnyLaws.lean) with that frame's names. The premise
"spare" (`W4M.mAny_isOther169`, there) holds at every interface and serves both frames. Limits: as
there.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Told.AnyLaws
import Johnson.Flat.Dec.TwoSizesAt

set_option autoImplicit false

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
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO} {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ} {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T₀ : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

set_option quotPrecheck false in
/-- The interface of the typed oracles over the three files. -/
local notation "Cf" => typedOracleCarrier ((threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P) (List Bool) (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).annT (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).annL

/-- Word, at the frame's carrier and wiring: two codings that differ in the entry file's code and the
six digests alone give one reading of every log. -/
theorem word_mAnyAtD (C : CK) (DKa DPa : WholeD)
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

#print axioms VerifiableInference.OnPublicFiles.word_mAnyAtD
