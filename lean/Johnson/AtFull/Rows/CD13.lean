-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CD13.lean: piece 13 of the 27 of «proof 0» at rowsW's written values, WALKED
CALL BY CALL WITH THE REST OF THE WRITTEN ROUNDS HANDED ON (Slice.lean: pieceD): from the table's
state 13 it ends at the table's state 14, and its calls' rounds are, by sameAll, the written rounds
from place 25122 to place 27001. A CLOSED FACT FOR LEAN's KERNEL («decide +kernel»: by evaluation in
Lean's kernel alone; no compiled code of this library is trusted), alone in its file. A law file; no
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

theorem pieceD_13 :
    pieceD sW (prW 0).rounds (tabW 13) (piecesW.getD 13 (pure ())) = some (tabW (13 + 1)) := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pieceD_13
