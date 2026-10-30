-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MFullQ.lean: AT THE FULL SIZE: **THE FAST FAMILY AT A PREPARED VALUE AND AT ANY bk**
  (famFQ), AND **bk AS A VALUE** (backFV | bkFV): so that what runs is the family of the m whose bk
  is one to one.
  famFQ ‹carF's letters› K O pr bk := W4M.famPrepQ pr bk O (hintK …) (needAt …)
    (Johnson/PV/MvPrepQ.lean over FamCutQ.lean)
  **famFQ_reads bk o q**: at pr := prepF … it IS what mF … bk reads out of gOf O: AT EVERY bk; no
    premise.
  serLF: a serialiser of the entry file's plain parts at the written link (the text of serLinkOf,
    declared nowhere in this library: the library's serPBL along the equation of the two markings)
  **backFV … K : StrCode (AllPts 256 (K + 1) ‹carF at lk := lkF, aL := aLF›)** :=
    ArmBack.backL2 at: sXF (Johnson/PV/SerReq.lean) with serRecFull twice · serBits · serLF |
    serKF | serPF: A TOTAL CODE: ONE TO ONE BY ITS TYPE (StrCode's own law)
  bkFV … K := (backFV … K).put · bkFV_is: it IS PV.MFull.bkF sXF serLF := rfl.
HOW TO CALL: let pr := prepF …; let bk := W4M.shoutAt (bkFV …) (= bkFV by shoutAt_eq := rfl; it
  shouts when read); F := famFQ … pr bk; m := mF … bk.
No soundness.


-/
import Johnson.PV.MFull
import Johnson.PV.MvPrepQ
import Johnson.PV.SerReq
import Johnson.Top.Fire.Code.Vals.EntryFive
import OnBytes.TypedOracleCompiler.Run.PageXFit
import OnBytes.K.Arm.SibMaps

set_option autoImplicit false
set_option maxRecDepth 40000

namespace PV.MFull
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run TypedOracleCompiler.Run.SerArm OnBytes.K.Arm.Pub VerifiableInference.OnPublicFiles
open VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Any
variable {X : Type} (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (lk : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX))
  (aL : RoundSplits (LvOf DK DP runK runP rK rP depthReq early lk).link.shape) (salt : ℕ)
  (K : ℕ) (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  (sp : X → ByteArray × ByteArray) (okS : X → Bool) (r₀ : RecFull) (c : ByteArray) (sR : ℕ)
  (linkF : FbIn 256 (carF DK DP runK runP rK rP depthReq early lk aL) .link × Fin (K + 1 + 1) →
      Option (List Bool)) (dK dP : Pd3)
  (bk : AllPts 256 (K + 1) (carF DK DP runK runP rK rP depthReq early lk aL) → List Bool) (O :
      ByteArray → ByteArray)

/-- **THE FAST FAMILY AT A PREPARED VALUE AND ANY bk.** -/
def famFQ (pr : W4M.Prep (carF DK DP runK runP rK rP depthReq early lk aL) (K + 1)) : Fam (typedOracleFamily 256
    (K + 1) (carF DK DP runK runP rK rP depthReq early lk aL)) :=
  W4M.famPrepQ pr bk O (W4M.hintK (K + 1) (DK.at frS.P.T.a)) (Johnson.RunOne.Lite.needAt (DP.at
      frS.P.T.a))

/-- **AT prepF IT IS WHAT mF … bk READS OUT OF THE HASH FUNCTION gOf O**: at every bk; point by
  point; no premise. -/
theorem famFQ_reads (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 (carF DK DP runK runP rK rP
                    depthReq early lk aL) o) :
    famFQ DK DP runK runP rK rP depthReq early lk aL K bk O (prepF DK DP runK runP rK rP depthReq
        early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP) o q =
      ((mF DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP
          bk).rng o).symm fun j =>
        TypedOracleCompiler.Run.PageRun.gOf O () ((mF DK DP runK runP rK rP depthReq early lk aL salt K h₀ k
                    c' sp okS r₀ c sR linkF dK dP bk).code o q j) :=
  W4M.famPrepQ_reads ..

end Any

/-- A serialiser of a plain part of some round of the written link. -/
def serLF : Ser (PlainPart (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf (ckP .two) PV.EntryFive.dsF))
    (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) PV.EntryFive.dsF))) :=
  Ser.ofEquiv (OnBytes.K.Arm.pbEq (_root_.Run.Twin.allLo_eq (TypedOracleCompiler.Run.PQ.SOf (ckP .two)
      PV.EntryFive.dsF)))
    (Ser.sum (Ser.sum Ser.unit Ser.unit) (TypedOracleCompiler.Run.PQ.serPBL (ckP .two) PV.EntryFive.dsF))

variable (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : (ReqAt Inst.Model.ppref) × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
      (depthReq : ℕ)
  (early : (ReqAt Inst.Model.ppref) → (ReqAt Inst.Model.ppref)) (K : ℕ)

/-- **THE TOTAL CODE BEHIND THE ESCAPE, AS A VALUE.** -/
def backFV : StrCode (AllPts 256 (K + 1) (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF
    PV.EntryFive.aLF)) :=
  TypedOracleCompiler.Run.ArmBack.backL2 (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF
              PV.EntryFive.aLF) (Ser.prod (Ser.option PV.SerReq.sXF) (Ser.prod serRecFull serRecFull))
    _root_.Compile.serBits
    (fun t => match t with
      | .link => serLF
      | .test => serKF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF
      | .onl => serPF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (K +
          1)

/-- **bk AS A VALUE.** -/
def bkFV : AllPts 256 (K + 1) (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF
    PV.EntryFive.aLF) → List Bool := (backFV DK DP runK runP rK rP depthReq early K).put

/-- It is bkF at the two serialisers sXF and serLF. -/
theorem bkFV_is : bkFV DK DP runK runP rK rP depthReq early K = bkF DK DP runK runP rK rP depthReq
    early PV.EntryFive.lkF PV.EntryFive.aLF K PV.SerReq.sXF serLF := rfl

end PV.MFull

#print axioms PV.MFull.famFQ_reads
#print axioms PV.MFull.bkFV_is
