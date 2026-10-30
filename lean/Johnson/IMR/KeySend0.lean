-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeySend0.lean: ONE CLOSED FACT, ALONE
IN ITS FILE, DECIDED BY LEAN's KERNEL: what sendsFrom's inner routine (IM.oneSend) returns for the
key file's chain 0 (18,851 rounds) at the typed sizes keyFull, the written setting's number of
samples and the written plan IS THE WRITTEN LIST keySendsFull.1: by the test PlanWritten.sameChain,
WHICH HOLDS EVERY FIELD (file · chain · codes · each sending's entry, label, sent, seed, behind) and
whose law sameChain_eq gives the equation (Johnson/Desc/Ok/PlanWritten/SendsTestLaws.lean). With a
bent twin that must say false. keyMade0 and sendIs: IMR/KeySendIs.lean. No soundness.
-/
import Johnson.IMR.KeySendIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open Johnson.G

set_option maxRecDepth 1000000 in
theorem key0_send : sendIs keyMade0 keySendsFull.1 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: against another chain's written list the test says no. -/
theorem key0_send_bent : sendIs keyMade0 keySendsFull.2.1 = false := by decide +kernel

end IM

#print axioms IM.key0_send
#print axioms IM.key0_send_bent
