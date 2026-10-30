-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyOwedSent.lean: ONE CLOSED FACT OF r6, ALONE
IN ITS FILE, DECIDED BY LEAN's KERNEL, with a bent twin that must say false: AN EQUATION, AS THE
FOLD GIVES IT: in the written list of the first chain's declared rounds (Johnson.KB8.declKeyFull.1:
18,851 rounds) the rounds in front of the first one named "BAT-sigma" (it is round 18,828) send FIVE
trees. rootsBefore · batchRound: Johnson/Desc/Key/Chain1.lean. No soundness.
-/
import Johnson.HB.LLHARD.KB8.Written
import Johnson.Desc.Key.Chain1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc.Key
open Johnson.KB8

set_option maxRecDepth 1000000 in
theorem sent_full : rootsBefore declKeyFull.1 (batchRound declKeyFull.1) = 5 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test. -/
theorem sent_bent : ¬ rootsBefore declKeyFull.1 (batchRound declKeyFull.1) = 6 := by
  decide +kernel

end IM

#print axioms IM.sent_full
#print axioms IM.sent_bent
