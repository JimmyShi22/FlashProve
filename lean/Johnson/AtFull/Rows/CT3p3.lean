-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/CT3p3.lean: THE TAIL: A NEGATIVE TEST; nothing uses it: the chain "entry
0" at its sendings, the LAST of them bent: the entry behind it takes in one answer more: refused
(evaluated beforehand: by the test (p3)). The count of sendings is unbent. A CLOSED FACT FOR LEAN's
KERNEL ("decide +kernel"; not by compiled code or its axiom), alone in its file. A law file; no
running text imports it. Made by program from one template. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.TailAtW

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open Johnson.AtFull.Sends (enR)

theorem tail_entry_p3 :
    tailPassB
      (enR.map fun d => { d with
        sends := d.sends.modify 4 fun x =>
          { x with behind := { x.behind with answers := x.behind.answers + 1 } } })
      twL3 = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tail_entry_p3
