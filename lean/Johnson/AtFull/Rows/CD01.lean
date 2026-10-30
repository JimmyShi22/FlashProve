-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CD01.lean: piece 1 of the 27 of «proof 0» at rowsW's written values, WALKED CALL
BY CALL WITH THE REST OF THE WRITTEN ROUNDS HANDED ON (Slice.lean: pieceD): from the table's state 1
it ends at the table's state 2, and its calls' rounds are, by sameAll, the written rounds from place
1980 to place 3859. A CLOSED FACT FOR LEAN's KERNEL («decide +kernel»: by evaluation in Lean's
kernel alone; no compiled code of this library is trusted), alone in its file. A law file; no
running text imports it. Made by program from one template. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.AtW
import Johnson.AtFull.Rows.Slice

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem pieceD_01 :
    pieceD sW (prW 0).rounds (tabW 1) (piecesW.getD 1 (pure ())) = some (tabW (1 + 1)) := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pieceD_01
