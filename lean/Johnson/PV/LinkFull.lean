-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/LinkFull.lean: THE VALUE FOR mS's ARGUMENT linkF AT THE FULL SIZE: W4M.linkPutC
  (Johnson/PV/LinkPut.lean) at the letters at which mPubTopFull lays ArmLinkCode.linkAt
  (Johnson/Top/Pub/ArmPublicTopFull.lean), general in the interface L2, whose
link's plain parts are handed over by pb2 (at carrierV LV (List Bool) AT aLF with lk := lkF:
  Equiv.refl _).
No «noncomputable» stands here: IT WANTS dsFull WITH CODE. c: the configuration's
  digest (32 bytes: hc); pdL: the entry's chain's parameters' digest.


-/
import Johnson.PV.LinkPut
import Johnson.Top.Pub.ArmPublicTopFull
import Johnson.Flat.ArmPlain

set_option autoImplicit false
set_option maxRecDepth 40000

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open OnBytes.Flat OnBytes.Slice OnBytes.Tie OnBytes.K.Arm OnBytes.K.Arm.Pub
open OnBytes.K.Left (sibLetters_full)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- The correspondence of the written link's plain parts with the description's, at the
  configuration's digest c: pubPbTopFull's text (Johnson/Top/Pub/ArmPublicTopFull.lean). -/
def pbFu (c : ByteArray) :=
  pbSib (entryXD recordGround c) (ckP .two) dsFull (sibLetters_full c).1 (sibLetters_full c).2.1

variable {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pb2 : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsFull))
      (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) dsFull)))

/-- **THE ENTRY FILE's CHAIN QUERIES' STRINGS, THE FULL SIZE.** -/
def linkFF (K : ℕ) (c : ByteArray) (hc : c.size = 32) (pdL : Dig 256) :
    FbIn 256 L2 .link × Fin (K + 1 + 1) → Option (List Bool) :=
  linkPutC (entryXD recordGround c) topD1Full c hc pdL (pubRestTopFull c) L2 (pb2.trans (pbFu c))
    (isPLAt (entryXD recordGround c) topD1Full L2 (pb2.trans (pbFu c))) (unA frS.P.v 1) (K + 1)

end W4M
