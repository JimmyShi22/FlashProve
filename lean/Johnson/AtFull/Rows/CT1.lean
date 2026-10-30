-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/CT1.lean: THE TAIL: the key file's second chain of sendings returns,
and at it the chain "key 1" passes the tail. A CLOSED FACT FOR LEAN's KERNEL ("decide +kernel"; not
by compiled code or its axiom), alone in its file. A law file; no running text imports it. Made by
program from one template. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.TailAtW

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open Johnson.AtFull.Sends (enR)

theorem tail_key1 : tailPassB k1N twL1 = true := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tail_key1
