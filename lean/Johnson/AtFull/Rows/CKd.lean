-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CKd.lean: «key 0» has 18,852 written rounds, said by two drops. A CLOSED FACT
FOR LEAN's KERNEL («decide +kernel»: by evaluation in Lean's kernel alone; no compiled code of this
library is trusted), alone in its file. A law file; no running text imports it. Made by program from
one template. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.AtW
import Johnson.AtFull.Rows.Slice

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem drops_k0 :
    (((kW 0).rounds.drop (18851 + 1)).isEmpty && !((kW 0).rounds.drop 18851).isEmpty) = true := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.drops_k0
