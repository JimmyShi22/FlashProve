-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MSmallQ.lean: AT THE SMALL SIZE: **THE FAST FAMILY AT A PREPARED VALUE AND AT ANY bk**
  (famSQ), AND **bk AS A VALUE** (backSV | bkSV): so that what runs is the family of the m whose bk
  is one to one: NO STUB.
  famSQ ‹carS's letters› K O pr bk := W4M.famPrepQ pr bk O (hintK …) (needAt …)
    (Johnson/PV/MvPrepQ.lean over FamCutQ.lean)
  **famSQ_reads bk o q**: at pr := prepS … it IS what mS … bk reads out of gOf O: AT EVERY bk; no
    premise.
  serLS: a serialiser of the entry file's plain parts at the written link (the text of serLinkOf,
    declared nowhere in this library: the library's serPBL along the equation of the two markings)
  **backSV … K : StrCode (AllPts 256 (K + 1) ‹carS at lk := lkS, aL := aLS›)** :=
    ArmBack.backL2 at: sXS (Johnson/PV/SerReq.lean) with serRecSmall twice · serBits · serLS |
    serKS | serPS: A TOTAL CODE: ONE TO ONE BY ITS TYPE (StrCode's own law)
  bkSV … K := (backSV … K).put · bkSV_is: it IS PV.MSmall.bkS sXS serLS := rfl.
HOW TO CALL: let pr := prepS …; let bk := W4M.shoutAt (bkSV …) (= bkSV by shoutAt_eq := rfl; it
  shouts when read); F := famSQ … pr bk; m := mS … bk.
No soundness.


-/
import Johnson.PV.MSmall
import Johnson.PV.MvPrepQ
import Johnson.PV.SerReq
import Johnson.Top.Fire.Code.Vals.EntryFive
import OnBytes.TypedOracleCompiler.Run.PageXFit
import OnBytes.K.Arm.SibMaps

set_option autoImplicit false
set_option maxRecDepth 40000

namespace PV.MSmall
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run TypedOracleCompiler.Run.SerArm OnBytes.K.Arm.Pub VerifiableInference.OnPublicFiles
open VerifiableInference.OnPublicFiles.SlotsBehindCutDS
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Any
variable {X : Type} (DK DP : WholeD) (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecSmall) (depthReq : ℕ)
  (early : X → X) (lk : InteractiveOracleProof (RecSmall × RecSmall) (twoExternalStrings (2 ^ srS.P.T.a) _root_.Run.PQ.SgX))
  (aL : RoundSplits (LvOf DK DP runK runP rK rP depthReq early lk).link.shape) (salt : ℕ)
  (K : ℕ) (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  (sp : X → ByteArray × ByteArray) (okS : X → Bool) (r₀ : RecSmall) (c : ByteArray) (sR : ℕ)
  (linkF : FbIn 256 (carS DK DP runK runP rK rP depthReq early lk aL) .link × Fin (K + 1 + 1) →
      Option (List Bool)) (dK dP : Pd3)
  (bk : AllPts 256 (K + 1) (carS DK DP runK runP rK rP depthReq early lk aL) → List Bool) (O :
      ByteArray → ByteArray)

/-- **THE FAST FAMILY AT A PREPARED VALUE AND ANY bk.** -/
def famSQ (pr : W4M.Prep (carS DK DP runK runP rK rP depthReq early lk aL) (K + 1)) : Fam (typedOracleFamily 256
    (K + 1) (carS DK DP runK runP rK rP depthReq early lk aL)) :=
  W4M.famPrepQ pr bk O (W4M.hintK (K + 1) (DK.at srS.P.T.a)) (Johnson.RunOne.Lite.needAt (DP.at
      srS.P.T.a))

/-- **AT prepS IT IS WHAT mS … bk READS OUT OF THE HASH FUNCTION gOf O**: at every bk; point by
  point; no premise. -/
theorem famSQ_reads (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 (carS DK DP runK runP rK rP
                    depthReq early lk aL) o) :
    famSQ DK DP runK runP rK rP depthReq early lk aL K bk O (prepS DK DP runK runP rK rP depthReq
        early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP) o q =
      ((mS DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP
          bk).rng o).symm fun j =>
        TypedOracleCompiler.Run.PageRun.gOf O () ((mS DK DP runK runP rK rP depthReq early lk aL salt K h₀ k
                    c' sp okS r₀ c sR linkF dK dP bk).code o q j) :=
  W4M.famPrepQ_reads ..

end Any

/-- A serialiser of a plain part of some round of the written link. -/
def serLS : Ser (PlainPart (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf (ckP .two) PV.EntryFive.dsS))
    (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) PV.EntryFive.dsS))) :=
  Ser.ofEquiv (OnBytes.K.Arm.pbEq (_root_.Run.Twin.allLo_eq (TypedOracleCompiler.Run.PQ.SOf (ckP .two)
      PV.EntryFive.dsS)))
    (Ser.sum (Ser.sum Ser.unit Ser.unit) (TypedOracleCompiler.Run.PQ.serPBL (ckP .two) PV.EntryFive.dsS))

variable (DK DP : WholeD) (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : (ReqAt sizesSmall) × RecSmall → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecSmall)
      (depthReq : ℕ)
  (early : (ReqAt sizesSmall) → (ReqAt sizesSmall)) (K : ℕ)

/-- **THE TOTAL CODE BEHIND THE ESCAPE, AS A VALUE.** -/
def backSV : StrCode (AllPts 256 (K + 1) (carS DK DP runK runP rK rP depthReq early PV.EntryFive.lkS
    PV.EntryFive.aLS)) :=
  TypedOracleCompiler.Run.ArmBack.backL2 (carS DK DP runK runP rK rP depthReq early PV.EntryFive.lkS
              PV.EntryFive.aLS) (Ser.prod (Ser.option PV.SerReq.sXS) (Ser.prod serRecSmall serRecSmall))
    _root_.Compile.serBits
    (fun t => match t with
      | .link => serLS
      | .test => serKS DK DP runK runP rK rP depthReq early PV.EntryFive.lkS PV.EntryFive.aLS
      | .onl => serPS DK DP runK runP rK rP depthReq early PV.EntryFive.lkS PV.EntryFive.aLS) (K +
          1)

/-- **bk AS A VALUE.** -/
def bkSV : AllPts 256 (K + 1) (carS DK DP runK runP rK rP depthReq early PV.EntryFive.lkS
    PV.EntryFive.aLS) → List Bool := (backSV DK DP runK runP rK rP depthReq early K).put

/-- It is bkS at our two serialisers. -/
theorem bkSV_is : bkSV DK DP runK runP rK rP depthReq early K = bkS DK DP runK runP rK rP depthReq
    early PV.EntryFive.lkS PV.EntryFive.aLS K PV.SerReq.sXS serLS := rfl

end PV.MSmall

#print axioms PV.MSmall.famSQ_reads
#print axioms PV.MSmall.bkSV_is
