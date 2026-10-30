-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/CT4.lean: THE TAIL: the light twin of "proof 0" passes the tail at
the written sendings of "proof 0" (82). A CLOSED FACT FOR LEAN's KERNEL ("decide +kernel"; not
by compiled code or its axiom), alone in its file. A law file; no running text imports it. Made by
program from one template. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.TailCut
import Johnson.AtFull.Rows.Twin
import Johnson.AtFull.Rows.AtW
import Johnson.G.SendsWritten

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem tail_proof0 :
    chainTailB sW
      (twinOf cW.sized.set "proof" 0 .request
        (proof0L cW (List.replicate 25 1) 13))
      proofSendsFull.1 = true := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tail_proof0
