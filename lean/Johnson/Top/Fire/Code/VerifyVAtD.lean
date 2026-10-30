-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/VerifyVAtD.lean: the verifier's side of an input of the full size in the
frame's make, at letters, as a value of `InputV` (its L, aT, Sd, W are those of
SlotsBehindCutD.lean), and `verifyV` at it, each as a definition without the mark `noncomputable`:
so Lean gives them code.
-/
import Johnson.Top.InputV
import Johnson.Top.Fire.Code.SlotsBehindCutD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1

variable {X : Type} (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
  (depthReq depthReqT : ℕ) (early : X → X)
  (lk : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX)) (K salt : ℕ)

local notation "LV" => LvOf DK DP runK runP rK rP depthReq early lk
local notation "AT" => aTOf DK DP runK runP rK rP depthReq early lk

/-- The verifier's side of an input in the frame's make, at letters. -/
def DvOf (aL : RoundSplits (LV).link.shape) (wL : ProtocolQueryLayout 256 (K + 1) (batLV LV aL))
    (embL : (p : OPos (LV).link.shape) → OSym (LV).link.shape p → List Bool)
    (prjL : (p : OPos (LV).link.shape) → List Bool → Option (OSym (LV).link.shape p))
    (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf (carrierV LV (List Bool) AT aL) t)
      (annOf (carrierV LV (List Bool) AT aL) t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params)
    (m : ImplV (typedOracleFamily 256 (K + 1) (carrierV LV (List Bool) AT aL)) 256)
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X) : InputV where
  X := X
  L := LV
  Bd := List Bool
  aT := AT
  aL := aL
  W := probe_WV DK DP runK runP rK rP depthReq depthReqT early lk K salt aL wL embL prjL
  Sd := probe_SdV DK DP runK runP rK rP depthReq early lk (K + 1) aL t cfg shape pl0 pl1 num seed
  cA := codeA (v := frS.P.v) (s := 1)
  r₀ := r₀
  p := p
  m := m
  enc := enc
  build := build

/-- The verifier at it. -/
def probe_verifyV (aL : RoundSplits (LV).link.shape) (wL : ProtocolQueryLayout 256 (K + 1) (batLV LV aL))
    (embL : (p : OPos (LV).link.shape) → OSym (LV).link.shape p → List Bool)
    (prjL : (p : OPos (LV).link.shape) → List Bool → Option (OSym (LV).link.shape p))
    (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf (carrierV LV (List Bool) AT aL) t)
      (annOf (carrierV LV (List Bool) AT aL) t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params)
    (m : ImplV (typedOracleFamily 256 (K + 1) (carrierV LV (List Bool) AT aL)) 256)
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X) :=
  verifyV (DvOf DK DP runK runP rK rP depthReq depthReqT early lk K salt aL wL embL prjL t cfg
    shape pl0 pl1 num seed r₀ p m enc build)

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.DvOf
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.probe_verifyV
#print axioms VerifiableInference.OnPublicFiles.verifyV
