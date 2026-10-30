-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/LeavesAt.lean: at a typed interface with a record whose leaves' bodies are
strings of bits (`typedOracleCarrier L (List Bool) aT aL`, Johnson/TypedOracleCompiler/RecCompile/Carrier.lean) the code of
leaf queries `leavesJ` (OnBytes/Maker/Page/LeafTakenAt.lean), read by the identity, writes the
string of the page's own call wherever it writes and that call returns.

Why. The page (OnBytes/Maker/Page/Frame.lean) takes a spelling of leaf queries from elsewhere, which
goes first. The laws on leaves ask that it be silent or write the page's own string. The interface
of the two makers' values and an entry's part (Johnson/Maker/Page/Type.lean, `LM`) is such a
carrier.

  `leavesC L0 nb cfg`: that code at the carrier.
  `agrees_leavesC`: what it writes is, as bytes, the string of the call of `leafOf fun b => b`,
    where that call returns.

What it asks. nb = 8 k: the file's salt has whole bytes.

What is not claimed. Where the code writes nothing, nothing is said. That the page's own call
returns where the code writes: Johnson/Maker/Page/LeavesWrites.lean. L0, nb, cfg are letters. That a
page's field `leafX` is this code is said of no page here.


-/
import OnBytes.Maker.Page.LeafTakenAt
import Johnson.TypedOracleCompiler.RecCompile.Carrier

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run TypedOracleCompiler.Run TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I0 X0 : Type} (L0 : _root_.Iop.BatchProtocol I0 X0) (nb k : ℕ) (hn : nb = 8 * k) (cfg : ByteArray)
  {I X : Type} {L : HolographicProtocol I X} (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)

/-- The code of leaf queries at the carrier, its bodies read as they are. -/
noncomputable def leavesC : PageG.Leaves (typedOracleCarrier L (List Bool) aT aL) :=
  leavesJ (L := typedOracleCarrier L (List Bool) aT aL) L0 nb cfg (Equiv.refl (List Bool))

include hn in
/-- **What it writes is the string of the page's own call, where that call returns.** -/
theorem agrees_leavesC (q : LeafIn (typedOracleCarrier L (List Bool) aT aL)) (s : List Bool) (c : Fmt.OQ)
    (h : (leavesC L0 nb cfg aT aL).lf.put q = some s)
    (hc : leafOf (L := typedOracleCarrier L (List Bool) aT aL) (fun b : List Bool => b) q = some c) :
    bitsToBytes s = strOf c :=
  agrees_leavesJ (L := typedOracleCarrier L (List Bool) aT aL) L0 nb k hn cfg (Equiv.refl (List Bool)) q s h c
    hc

end OnBytes.Maker.Page
