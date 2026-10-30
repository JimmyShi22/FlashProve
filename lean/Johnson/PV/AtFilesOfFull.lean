-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/AtFilesOfFull.lean: `mOne` (Johnson/PV/MemberOne.lean) at the carrier of the frame at the
  full size: `typedOracleCarrier ((threeProtocolsWithFixedLinkAtFullSize ..).withProvers P) (List Bool) annT annL`
  (Johnson/Flat/WiresAtSizes.lean).

`mOne` is general in the object, so nothing is unfolded: the object is laid for the letter L; the
  read-backs are `some`. The type of `back` here is the type of that file's `backOfFull`.
Limits: those of Johnson/PV/MemberOne.lean.

-/
import Johnson.PV.MemberOne
import Johnson.Flat.WiresAtSizes

set_option autoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open OnBytes.K.Arm.ProofFront
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ) (P : (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early
      salt).Provers)

/-- The interface of the typed oracles over the three files: the text of `carOfFull`
(Johnson/Flat/WiresAtSizes.lean). -/
abbrev carW4 := typedOracleCarrier ((threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).withProvers P) (List
                                                Bool) (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).annT (threeProtocolsWithFixedLinkAtFullSize A R DK DP
                                                                          runK runP rK rP depthReq early salt).annL

variable {K : ℕ} (h₀ : HId) (k : OnBytes.Params.KeyChains) (c : OnBytes.Params.ProofChains)
  {sp : X → ByteArray × ByteArray} {r₀ : ((threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early
      salt).withProvers P).Rec} (S : FrontSet ((threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early
              salt).withProvers P) sp r₀)
  (tlK tlP : Dig 256 → List OnBytes.E → List (Dig 256)) (cfg : ByteArray) (sR : ℕ)
  (p0 p1 : PBt (carW4 A R DK DP runK runP rK rP depthReq early salt P) .test) (isP0 isP1 : PBt
      (carW4 A R DK DP runK runP rK rP depthReq early salt P) .test → Bool) (cfgL : List (Dig 256))
      (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (Lk : LinkCode (carW4 A R DK DP runK runP rK rP depthReq early salt P) (K + 1)) (V : Leaves (carW4
      A R DK DP runK runP rK rP depthReq early salt P)) (dK dP : Pd3)

/-- **THE ONE CODING AT THAT CARRIER.** -/
def mOfFull (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
    (hK : K + 1 + 1 < 2 ^ 49) (hc : cfg.size = OnBytes.K.Arm.digBytes)
    (hL : Lk.l ∉ [OnBytes.Params.labelOneTime, OnBytes.Params.labelShared,
      OnBytes.Params.labelSecond, OnBytes.Params.labelFirst, OnBytes.Params.labelSharedProof,
      OnBytes.Params.labelSecondProof])
    (back : StrCode (AllPts 256 (K + 1) (carW4 A R DK DP runK runP rK rP depthReq early salt P))) :
        OracleCoding (typedOracleFamily 256 (K + 1) (carW4 A R DK DP runK runP rK rP depthReq early salt P)) 256 :=
  mOne (L := (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).withProvers P) (List Bool)
      (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).annT (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK
                                runP rK rP depthReq early salt).annL (ckP .two) (DK.at frS.P.T.a)
    (DP.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty (front₀ rP) (join₀ rP) ByteArray.empty
    (fun z => some z) (fun z => some z) h₀ k c S tlK tlP cfg sR (fun b => b) p0 p1 isP0 isP1 cfgL sh
        hp0
    hp1 rest Lk V dK dP (fun _ _ _ h h' => Option.some.inj (h.trans h'.symm))
    (fun _ _ _ h h' => Option.some.inj (h.trans h'.symm)) hDK hDP hK hc hL back

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.mOfFull
