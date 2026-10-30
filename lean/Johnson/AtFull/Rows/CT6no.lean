-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/CT6no.lean: THE TAIL: A NEGATIVE TEST; nothing uses it: the chain "proof 2" at
the written sendings of "proof 1" is rejected. A SHALLOW NEGATIVE TEST: by reading (Lean says only
"false"), it is rejected at the count of sendings (4 against 9): it shows nothing on the tests
inside a sending. A CLOSED FACT FOR LEAN's KERNEL ("decide +kernel"; not by compiled code or its
axiom), alone in its file. A law file; no running text imports it. Made by program from one
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

theorem tail_proof2_no :
    chainTailB sW
      (twinOf cW.sized.set "proof" 2 (scOf cW.sized.proof.batch .request)
        (proof2R cW))
      proofSendsFull.2.1 = false := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tail_proof2_no
