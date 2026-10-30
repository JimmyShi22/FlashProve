-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/ArmsAtCarrierX.lean: the two laws of ArmsAtCarrier.lean with the verifier over
the lesser wire records on the left (`verifyWholeX`, OnBytes/Maker/LessWhole.lean), at the full
size. `carrierAtX`: at a parser's carrier: no where no string is laid; else `verifyWholeX` at the
string and the two lists off the same carrier. `carrierAtX_eq`: it is `verifyCarrierAt`, at all
letters; no premise. `keyArm_carrierX`, `proofArm_carrierX`: so it is `vTAV`, `vBAV` at
SlotsBehindCutD.lean's letters.

-/
import Johnson.Top.Fire.Code.ArmsAtCarrier
import OnBytes.Maker.LessWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable {TF TJ T3 Xi : Type} (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
  {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- The verifier of a whole file over the lesser wire records, at a carrier and the binding tree's
shape. -/
def carrierAtX (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (s : Params.LinBindingShape) (cms : List (Dig 256))
    (x : Xi) (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) :
    TypedOracleComputation 256 (K + 1) L Bool :=
  (k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3).elim (pure false) fun π =>
    verifyWholeX C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s.logLeaves cms x π
      (ownOfCarrier D k) (listedOfCarrier D.a k)

/-- It is the verifier along lists at the carrier. No premise. -/
theorem carrierAtX_eq (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (s : Params.LinBindingShape) (cms : List (Dig 256))
    (x : Xi) (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) :
    carrierAtX C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s cms x k cfg pF pJ p3 =
      verifyCarrierAt C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s cms x k cfg pF
        pJ p3 := by
  unfold carrierAtX verifyCarrierAt
  exact congrArg _ (funext fun π => verifyWholeX_eq C K chal D tF tJ t3 silent run sMT sFS t embS
    embP xin embE s.logLeaves cms x π _ _)

end OnBytes.Maker

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS)

/-- (T) **The key's arm at a carrier, over the lesser wire records.** -/
theorem keyArm_carrierX {X : Type} (DK DP : WholeD)
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
    carrierAtX
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
  rw [carrierAtX_eq]
  exact keyArm_carrier DK DP runK runP rK rP depthReq early lk K salt aL wL embL prjL cA p cm rec s
    k cfg pF pJ p3

/-- (B) **The proof's arm at a carrier, over the lesser wire records.** -/
theorem proofArm_carrierX {X : Type} (DK DP : WholeD)
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
    carrierAtX
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
  rw [carrierAtX_eq]
  exact proofArm_carrier DK DP runK runP rK rP depthReqT early lk K salt s aL wL embL prjL cA r₀ p
    cm x rec k cfg pF pJ p3

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms OnBytes.Maker.carrierAtX_eq
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.keyArm_carrierX
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.proofArm_carrierX
