-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/CT5.lean: THE TAIL: the chain "proof 1" passes the tail at its
written sendings. A CLOSED FACT FOR LEAN's KERNEL ("decide +kernel"; not by compiled code or
its axiom), alone in its file. A law file; no running text imports it. Made by program from one
template. Nothing on soundness or on hiding.

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

theorem tail_proof1 :
    chainTailB sW
      (twinOf cW.sized.set "proof" 1 (scOf cW.sized.proof.batch .shared)
        (proof1R cW))
      proofSendsFull.2.1 = true := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tail_proof1
