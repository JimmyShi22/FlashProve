-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/CT6id.lean: THE TAIL: A POSITIVE TEST; nothing uses it: the chain "proof
2" at its written sendings, with the bending function at the identity: it passes: so what refuses in
the three sister files is the bend, not the bending. A CLOSED FACT FOR LEAN's KERNEL ("decide
+kernel"; not by compiled code or its axiom), alone in its file. A law file; no running text imports
it. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.TailBend

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem tail_proof2_same :
    chainTailB sW
      { twL6 with
        calls := bendCs
          (fun y c => (y, c))
          twL6.calls }
      proofSendsFull.2.2 = true := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tail_proof2_same
