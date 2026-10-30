-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/LinkSmall.lean: THE VALUE FOR mS's ARGUMENT linkF AT THE SMALL SIZE: W4M.linkPutC
  (Johnson/PV/LinkPut.lean) at the letters at which mPubTopSmall (ArmPublicTopSmall.lean) lays
  linkAt (OnBytes/TypedOracleCompiler/Slice/ArmLinkCode.lean), general in the interface L2, whose
link's plain parts are handed over by pb2 (at carrierV LV (List Bool) AT aLS with lk := lkS:
  Equiv.refl _).
No «noncomputable» stands here: IT WANTS dsSmall WITH CODE. c: the configuration's
  digest (32 bytes: hc); pdL: the entry's chain's parameters' digest.


-/
import Johnson.PV.LinkPut
import Johnson.Top.Pub.ArmPublicTopSmall
import Johnson.Flat.ArmPlain

set_option autoImplicit false
set_option maxRecDepth 40000

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open OnBytes.Flat OnBytes.Slice OnBytes.Tie OnBytes.K.Arm OnBytes.K.Arm.Pub
open OnBytes.K.Left (sibLetters_small)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- The correspondence of the written link's plain parts with the description's, at the
  configuration's digest c: the text of pubPbTopSmall (ArmPublicTopSmall.lean). -/
def pbS (c : ByteArray) :=
  pbSib (entryXD smallRecordGround c) (ckP .two) dsSmall (sibLetters_small c).1 (sibLetters_small
      c).2.1

variable {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pb2 : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsSmall))
      (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsSmall)))

/-- **THE ENTRY FILE's CHAIN QUERIES' STRINGS, THE SMALL SIZE.** -/
def linkFS (K : ℕ) (c : ByteArray) (hc : c.size = 32) (pdL : Dig 256) :
    FbIn 256 L2 .link × Fin (K + 1 + 1) → Option (List Bool) :=
  linkPutC (entryXD smallRecordGround c) topD1Small c hc pdL (pubRestTopSmall c) L2 (pb2.trans (pbS
      c))
    (isPLAt (entryXD smallRecordGround c) topD1Small L2 (pb2.trans (pbS c))) (unA srS.P.v 1) (K + 1)

end W4M
