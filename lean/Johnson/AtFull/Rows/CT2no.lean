-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/CT2no.lean: THE TAIL: A NEGATIVE TEST; nothing uses it: the chain "key 1" at the
sendings of "key 2" is rejected. A SHALLOW NEGATIVE TEST: going by the written lists' counts (9
against 4) it is rejected at the count of sendings; Lean says only "false". It shows nothing on the
tests inside a sending. A CLOSED FACT FOR LEAN's KERNEL ("decide +kernel"; not by compiled code or
its axiom), alone in its file. A law file; no running text imports it. Made by program from one
template. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.TailAtW

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open Johnson.AtFull.Sends (enR)

theorem tail_key2_no : tailPassB k2N twL1 = false := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tail_key2_no
