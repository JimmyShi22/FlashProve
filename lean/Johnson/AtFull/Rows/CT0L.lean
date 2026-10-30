-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CT0L.lean: the light twin of «key 0» (Twin.lean: key0L: «pure ()» for the loop
of the lookups) returns and ends at counters 0. A CLOSED FACT FOR LEAN's KERNEL («decide +kernel»:
by evaluation in Lean's kernel alone; no compiled code of this library is trusted), alone in its
file. A law file; no running text imports it. Made by program from one template. Nothing on
soundness or on hiding.
-/
import Johnson.AtFull.Rows.AtW
import Johnson.AtFull.Rows.Twin

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem twinL_key0 :
    endOf sW ⟨.once, 0, 0, 0⟩ (key0L cW) = some ⟨.once, 0, 0, 0⟩ := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.twinL_key0
