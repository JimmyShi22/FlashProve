-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CCtlB.lean: A CONTROL; nothing uses it: THE PIECE's TEST CAN SAY NO: piece 1 of
«proof 0», held against the written rounds from place 0 on (piece 0's), is refused. The test here is
pieceC, which is pieceD by Slice.lean's pieceD_eq. That the routine itself returns from this small
state is pieceD_01's word (CD01.lean): so the «none» comes of a round that differs, not of a
refusal. A CLOSED FACT FOR LEAN's KERNEL («decide +kernel»: by evaluation in Lean's kernel alone; no
compiled code of this library is trusted), alone in its file. A law file; no running text imports
it. Made by program from one template. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.AtW
import Johnson.AtFull.Rows.StepC

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem control_other :
    pieceC sW (prW 0).rounds (⟨.request, 0, 0, 0⟩, 0) (piecesW.getD 1 (pure ())) = none := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.control_other
