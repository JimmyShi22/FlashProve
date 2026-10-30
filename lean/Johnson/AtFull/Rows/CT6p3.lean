-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/CT6p3.lean: THE TAIL: A NEGATIVE TEST; nothing uses it: the chain "proof
2" at its written sendings, the LAST of the four bent: the entry behind it takes in one answer more:
refused (evaluated beforehand: by the test (p3)). The count of sendings is unbent: so the refusal
comes from inside a sending, not from the first test. A CLOSED FACT FOR LEAN's KERNEL ("decide
+kernel"; not by compiled code or its axiom), alone in its file. A law file; no running text imports
it. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.TailAtW

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem tail_proof2_p3 :
    chainTailB sW twL6
      { proofSendsFull.2.2 with
        sends := proofSendsFull.2.2.sends.modify 3 fun x =>
          { x with behind := { x.behind with answers := x.behind.answers + 1 } } } = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tail_proof2_p3
