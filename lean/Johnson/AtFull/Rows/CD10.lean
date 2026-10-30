-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CD10.lean: piece 10 of the 27 of «proof 0» at rowsW's written values, WALKED
CALL BY CALL WITH THE REST OF THE WRITTEN ROUNDS HANDED ON (Slice.lean: pieceD): from the table's
state 10 it ends at the table's state 11, and its calls' rounds are, by sameAll, the written rounds
from place 19287 to place 21265. A CLOSED FACT FOR LEAN's KERNEL («decide +kernel»: by evaluation in
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

theorem pieceD_10 :
    pieceD sW (prW 0).rounds (tabW 10) (piecesW.getD 10 (pure ())) = some (tabW (10 + 1)) := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pieceD_10
