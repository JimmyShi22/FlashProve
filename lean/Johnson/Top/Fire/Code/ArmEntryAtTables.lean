-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/ArmEntryAtTables.lean: over SlotsBehindCutD.lean's letters, with the entry
file's five at the written link's make (`linkProtocolOfRoundData`; `allLo`; `wqW`; `embT`, `prjT`): the entry's arm of
the verifier (`vLAV`), at a string that `assembleW` lays of a chain as read and two tables, has at
every family F of typed oracle functions the value of the fourteen lines of the form to run
(`stagesWL`, Johnson/RunOne/StrictLinkWL.lean). One premise: the string has been laid.

-/
import Johnson.Top.Fire.Code.SlotsBehindCutD
import Johnson.RunOne.StrictLinkWL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS SOf)
open Johnson.RunOne.StrictW (wqW assembleW stagesWL stagesWL_yes)

/-- (E) **The entry's arm at a string laid of a chain as read and two tables.** -/
theorem entryArm_tables {X : Type} (DK DP : WholeD)
    (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
    (depthReq depthReqT : ℕ) (early : X → X) (ds : List TypedOracleCompiler.Run.PQ.RD)
    (xs : List _root_.Run.PQ.XO) (dec : RecFull × RecFull → PQ.View → Bool) (K salt : ℕ)
    (cA : (LvOf DK DP runK runP rK rP depthReq early (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec)).Ans →
      List (Dig 256))
    (p : _root_.Compile.Params) (cm cm' : Dig 256)
    (rec rec' :
      (LvOf DK DP runK runP rK rP depthReq early (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec)).Rec)
    (cfg : ByteArray) (o : _root_.Fmt.ChainOut) (tab tx : Johnson.RunOne.StrictB.Tab)
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData (ckP .two) ds frS.P.T.a xs dec).up)
    (h : assembleW (ckP .two) ds frS.P.T.a xs dec cfg o tab tx = some π)
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1)
      (carrierV (LvOf DK DP runK runP rK rP depthReq early (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec))
        (List Bool)
        (aTOf DK DP runK runP rK rP depthReq early (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec))
        (_root_.Run.Twin.allLo (SOf (ckP .two) ds))))) :
    ((stagesWL (ckP .two) ds frS.P.T.a xs dec K (chalP .two K)
        (carrierV (LvOf DK DP runK runP rK rP depthReq early (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec))
          (List Bool)
          (aTOf DK DP runK runP rK rP depthReq early (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec))
          (_root_.Run.Twin.allLo (SOf (ckP .two) ds)))
        p.sMT p.sFS (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds) id (fun _ => none)
        (bodyS frS.P.T.a salt).embE 0 F (cmsLAV cA cm cm' rec.2 rec'.2) (rec, rec') π tab tx).map
        OnBytes.Maker.Steps.yes).getD false =
      (vLAV (probe_WV DK DP runK runP rK rP depthReq depthReqT early
          (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec) K salt (_root_.Run.Twin.allLo (SOf (ckP .two) ds))
          (wqW (ckP .two) ds frS.P.T.a xs dec K (chalP .two K))
          (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds)
          (TypedOracleCompiler.StringsList.prjT salt (ckP .two) ds))
        cA p cm cm' rec rec' π).det F := by
  rw [stagesWL_yes (ckP .two) ds frS.P.T.a xs dec K (chalP .two K) _ p.sMT p.sFS _ id
    (fun _ => none) _ 0 F _ (rec, rec') cfg o tab tx π h]
  rfl

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.entryArm_tables
