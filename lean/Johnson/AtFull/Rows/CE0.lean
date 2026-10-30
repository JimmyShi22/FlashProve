-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CE0.lean: the chain «entry 0» whole, as one piece, at rowsW's written values: it
ends at counters 0 and its rounds are, by sameAll, all its written rounds. A CLOSED FACT FOR LEAN's
KERNEL («decide +kernel»: by evaluation in Lean's kernel alone; no compiled code of this library is
trusted), alone in its file. A law file; no running text imports it. Made by program from one
template. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.AtW

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem entry_whole :
    pieceB sW (cW.entry).rounds (⟨.once, 0, 0, 0⟩, 0) (entryR cW) =
      some (⟨.once, 0, 0, 0⟩, (cW.entry).rounds.length) := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.entry_whole
