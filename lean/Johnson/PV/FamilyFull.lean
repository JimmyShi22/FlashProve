-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/FamilyFull.lean: the letters of `mOfFull` (Johnson/PV/AtFilesOfFull.lean) laid by terms
  of the library, at the full size, general in both files' rounds' data and both decisions: a family
  of codings over the public digests.

  Lk: the entry file's chain queries: `linkAt` (OnBytes/TypedOracleCompiler/Slice/ArmLinkCode.lean): the very code
    inside the entry's arm's own encoding (`implL2_linkAt`), at the letters at which `mPubTopFull`
    lays it (Johnson/Top/Pub/ArmPublicTopFull.lean).
  V: the leaves: `leavesC` (Johnson/Maker/Page/LeavesAt.lean).
  The seeds' two queries: the plain part `plainFirst`; the tests by the serialiser (`isAt`,
    Johnson/Flat/ArmPlain.lean); cfgL, sh, rest as `pubFull` lays them
    (Johnson/Top/KeyCutArmD.lean).
  tlK: the code of the answers, as `cutArmFullD` lays it (Johnson/Top/KeyCutArmD.lean).
  tlP: `tlAns` (Johnson/Flat/TailAns.lean): the root again, then each answer as a digest.
The index: the configuration's digest c (32 bytes), the entry's parameters' digest pdL, the six
  digests dK, dP.
Letters that are left: S (the front set), back, sR, L0, and k, c', h₀ (read for the six digests
  alone, which dK and dP overwrite).
Limits: those of Johnson/PV/CutAll.lean and Johnson/PV/MemberOne.lean. Nothing on soundness.

-/
import Johnson.PV.AtFilesOfFull
import Johnson.Top.Pub.ArmPublicTopFull
import Johnson.Maker.Page.LeavesAt
import OnBytes.TypedOracleCompiler.Slice.ArmLinkCode
import Johnson.Flat.SerArmAt
import OnBytes.K.KeyAnswers
import Johnson.Flat.TailAns

set_option autoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run TypedOracleCompiler.Slice TypedOracleCompiler.Run.SerArm OnBytes.Tie OnBytes.K.Arm
    OnBytes.K.Arm.Pub
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Slice.ArmLinkCode (linkAt)
open OnBytes.K.Left (sibLetters_full)
open OnBytes.K.Arm.ProofFront
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ) (P : (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early
      salt).Provers)

/-- THE ENTRY FILE's CODE, at the configuration's digest c and the entry's parameters' digest pdL.
-/
def lkOfFull (K : ℕ) (c : ByteArray) (hc : c.size = 32) (pdL : Dig 256) : LinkCode (carW4 A R DK DP
    runK runP rK rP depthReq early salt P) (K + 1) :=
  linkAt (entryXD recordGround c) topD1Full c hc pdL (pubRestTopFull c) (carW4 A R DK DP runK runP
      rK rP depthReq early salt P) (pubPbTopFull c)
    (isPLAt (entryXD recordGround c) topD1Full (carW4 A R DK DP runK runP rK rP depthReq early salt
        P) (pubPbTopFull c))
    (hpLAt (entryXD recordGround c) topD1Full (carW4 A R DK DP runK runP rK rP depthReq early salt
        P) (pubPbTopFull c))
    (codeA (v := frS.P.v) (s := 1)) OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans
        (codeA_length a').symm)
    trAns_sib_inj (K + 1)

/-- Its label is the format's label of a link's chain. -/
theorem lkOfFull_l (K : ℕ) (c : ByteArray) (hc : c.size = 32) (pdL : Dig 256) :
    (lkOfFull A R DK DP runK runP rK rP depthReq early salt P K c hc pdL).l =
        OnBytes.Params.labelLink := rfl

/-- THE LEAVES' CODE. -/
def vOfFull {I0 X0 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0) (c : ByteArray) : Leaves (carW4 A R DK DP
              runK runP rK rP depthReq early salt P) :=
  leavesC (L := (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).withProvers P) L0 (8 * salt) c
      (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).annT (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK
                                runP rK rP depthReq early salt).annL

/-- The serialiser of the key file's plain parts. -/
def serKOfFull : Ser (PBt (carW4 A R DK DP runK runP rK rP depthReq early salt P) .test) :=
  serWhole (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
    (serFront (Ser.list serE3)) (serJoin (Ser.list serE3) serBytes) serBytes

/-- The plain part of the seeds' two queries. -/
def p0OfFull : PBt (carW4 A R DK DP runK runP rK rP depthReq early salt P) .test :=
    TypedOracleCompiler.Run.SeedVals.plainFirst _ _ _ _

variable {K : ℕ} (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  {sp : X → ByteArray × ByteArray} {r₀ : ((threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early
      salt).withProvers P).Rec} (S : FrontSet ((threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early
              salt).withProvers P) sp r₀)
  (sR : ℕ) {I0 X0 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0)

/-- **THE FAMILY OF THE ONE CODING OVER THE PUBLIC DIGESTS, AT THE FULL SIZE, AT EVERY DATA AND
EVERY TWO DECISIONS.** -/
def mFamilyFull (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
    (hK : K + 1 + 1 < 2 ^ 49) (back : ByteArray → StrCode (AllPts 256 (K + 1) (carW4 A R DK DP runK
        runP rK rP depthReq early salt P)))
    (c : ByteArray) (hc : c.size = 32) (pdL : Dig 256) (dK dP : Pd3) :
    OracleCoding (typedOracleFamily 256 (K + 1) (carW4 A R DK DP runK runP rK rP depthReq early salt P)) 256 :=
  mOfFull A R DK DP runK runP rK rP depthReq early salt P h₀ k c' S (fun _ l => OnBytes.K.cAL
      frS.P.v 1 l)
    tlAns c sR (p0OfFull A R DK DP runK runP rK rP depthReq early salt P) (p0OfFull A R DK DP runK
        runP rK rP depthReq early salt P)
    (isAt (serKOfFull A R DK DP runK runP rK rP depthReq early salt P) (p0OfFull A R DK DP runK runP
        rK rP depthReq early salt P)) (isAt (serKOfFull A R DK DP runK runP rK rP depthReq early
        salt P) (p0OfFull A R DK DP runK runP rK rP depthReq early salt P))
    (TypedOracleCompiler.Run.SeedVals.cfgL c) pubShapeTopFull
    (isAt_iff (serKOfFull A R DK DP runK runP rK rP depthReq early salt P) (p0OfFull A R DK DP runK
        runP rK rP depthReq early salt P)) (isAt_iff (serKOfFull A R DK DP runK runP rK rP depthReq
        early salt P) (p0OfFull A R DK DP runK runP rK rP depthReq early salt P))
    (pubRestTopFull c) (lkOfFull A R DK DP runK runP rK rP depthReq early salt P K c hc pdL)
        (vOfFull A R DK DP runK runP rK rP depthReq early salt P L0 c) dK dP hDK hDP hK hc
    (by rw [lkOfFull_l]; decide) (back c)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.lkOfFull_l
#print axioms VerifiableInference.OnPublicFiles.mFamilyFull
