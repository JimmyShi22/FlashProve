-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/ArmsAtCarrier.lean: over SlotsBehindCutD.lean's letters: at the verifier's
side of the full size's object in the frame's make, and the wire record written out there, the key's
arm and the proof's arm of the verifier (`vTAV`, `vBAV`) at the string that is laid of a parser's
carrier are the verifier along lists at that carrier (`verifyCarrierAt`,
OnBytes/Maker/ListedCarrierTop.lean), as trees of queries. No premise on the carrier. Where no
string is laid the listed form says no.

-/
import Johnson.Top.Fire.Code.SlotsBehindCutD
import OnBytes.Maker.ListedCarrierTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS)

/-- (T) **The key's arm at a carrier.** -/
theorem keyArm_carrier {X : Type} (DK DP : WholeD)
    (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
    (depthReq : ℕ) (early : X → X)
    (lk : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX)) (K salt : ℕ)
    (aL : RoundSplits (LvOf DK DP runK runP rK rP depthReq early lk).link.shape)
    (wL : ProtocolQueryLayout 256 (K + 1) (batLV (LvOf DK DP runK runP rK rP depthReq early lk) aL))
    (embL : (p : OPos (LvOf DK DP runK runP rK rP depthReq early lk).link.shape) →
      OSym (LvOf DK DP runK runP rK rP depthReq early lk).link.shape p → List Bool)
    (prjL : (p : OPos (LvOf DK DP runK runP rK rP depthReq early lk).link.shape) → List Bool →
      Option (OSym (LvOf DK DP runK runP rK rP depthReq early lk).link.shape p))
    (cA : (LvOf DK DP runK runP rK rP depthReq early lk).Ans → List (Dig 256))
    (p : _root_.Compile.Params) (cm : Dig 256)
    (rec : (LvOf DK DP runK runP rK rP depthReq early lk).Rec)
    (s : OnBytes.Params.LinBindingShape) (k : Carrier.File) (cfg : ByteArray)
    (pF : FrontMsg (List OnBytes.E)) (pJ : _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
    (p3 : ByteArray) :
    verifyCarrierAt
        (L := carrierV (LvOf DK DP runK runP rK rP depthReq early lk) (List Bool)
          (aTOf DK DP runK runP rK rP depthReq early lk) aL)
        (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK
        runK p.sMT p.sFS Tag.test
        (probe_WV DK DP runK runP rK rP depthReq s.logLeaves early lk K salt aL wL embL prjL).embT
        id (fun _ => none)
        (probe_WV DK DP runK runP rK rP depthReq s.logLeaves early lk K salt aL wL embL prjL).embE
        s (cmsTAV cA cm rec.2) rec k cfg pF pJ p3 =
      (k.toBPrfAt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK cfg
          s pF pJ p3).elim (pure false) fun π =>
        vTAV (probe_WV DK DP runK runP rK rP depthReq s.logLeaves early lk K salt aL wL embL prjL)
          cA p cm rec π := by
  rw [verifyCarrierAt_is]
  rfl

/-- (B) **The proof's arm at a carrier.** -/
theorem proofArm_carrier {X : Type} (DK DP : WholeD)
    (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
    (depthReqT : ℕ) (early : X → X)
    (lk : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX)) (K salt : ℕ)
    (s : OnBytes.Params.LinBindingShape)
    (aL : RoundSplits (LvOf DK DP runK runP rK rP s.logLeaves early lk).link.shape)
    (wL : ProtocolQueryLayout 256 (K + 1) (batLV (LvOf DK DP runK runP rK rP s.logLeaves early lk) aL))
    (embL : (p : OPos (LvOf DK DP runK runP rK rP s.logLeaves early lk).link.shape) →
      OSym (LvOf DK DP runK runP rK rP s.logLeaves early lk).link.shape p → List Bool)
    (prjL : (p : OPos (LvOf DK DP runK runP rK rP s.logLeaves early lk).link.shape) → List Bool →
      Option (OSym (LvOf DK DP runK runP rK rP s.logLeaves early lk).link.shape p))
    (cA : (LvOf DK DP runK runP rK rP s.logLeaves early lk).Ans → List (Dig 256))
    (r₀ : (LvOf DK DP runK runP rK rP s.logLeaves early lk).Rec)
    (p : _root_.Compile.Params) (cm : Dig 256) (x : X)
    (rec : (LvOf DK DP runK runP rK rP s.logLeaves early lk).Rec)
    (k : Carrier.File) (cfg : ByteArray)
    (pF : FrontMsg (List OnBytes.E)) (pJ : _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
    (p3 : ByteArray) :
    verifyCarrierAt
        (L := carrierV (LvOf DK DP runK runP rK rP s.logLeaves early lk) (List Bool)
          (aTOf DK DP runK runP rK rP s.logLeaves early lk) aL)
        (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
        runP p.sMT p.sFS Tag.onl
        (probe_WV DK DP runK runP rK rP s.logLeaves depthReqT early lk K salt aL wL embL prjL).embB
        id (xinBAV r₀)
        (probe_WV DK DP runK runP rK rP s.logLeaves depthReqT early lk K salt aL wL embL prjL).embE
        s (cmsBAV cA cm rec.2) (x, rec) k cfg pF pJ p3 =
      (k.toBPrfAt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP cfg
          s pF pJ p3).elim (pure false) fun π =>
        vBAV (probe_WV DK DP runK runP rK rP s.logLeaves depthReqT early lk K salt aL wL embL prjL)
          cA r₀ p cm x rec π := by
  rw [verifyCarrierAt_is]
  rfl

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.keyArm_carrier
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.proofArm_carrier
