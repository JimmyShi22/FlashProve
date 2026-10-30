-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CCtlA.lean: A CONTROL; nothing uses it: THE PIECE's TEST CAN SAY NO: piece 0 of
«proof 0», held against the written rounds from place 1 on instead of place 0, is refused. The test
here is pieceC, which is pieceD by Slice.lean's pieceD_eq. That the routine itself returns from this
small state is pieceD_00's word (CD00.lean): so the «none» comes of a round that differs, not of a
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

theorem control_shifted :
    pieceC sW (prW 0).rounds (⟨.request, 0, 0, 0⟩, 1) (piecesW.getD 0 (pure ())) = none := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.control_shifted
