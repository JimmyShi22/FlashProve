-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/CT1p4.lean: THE TAIL: A NEGATIVE TEST; nothing uses it: the chain "key 1"
at its sendings, the FIRST of them bent: its entry draws one element more: refused (evaluated
beforehand: by the test (p4)). The count of sendings is unbent. A CLOSED FACT FOR LEAN's KERNEL
("decide +kernel"; not by compiled code or its axiom), alone in its file. A law file; no running
text imports it. Made by program from one template. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.TailAtW

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open Johnson.AtFull.Sends (enR)

theorem tail_key1_p4 :
    tailPassB
      (k1N.map fun d => { d with
        sends := d.sends.modify 0 fun x =>
          { x with seed := { x.seed with drawE := x.seed.drawE + 1 } } })
      twL1 = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tail_key1_p4
