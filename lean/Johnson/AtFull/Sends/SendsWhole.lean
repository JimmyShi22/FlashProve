-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/SendsWhole.lean: THE HEAD's EXAMPLE: THE SENDINGS AS A VALUE AT THE WRITTEN
PARTS, WITH NO PREMISE LEFT: `Johnson.G.sendsFrom` at W := writtenMade.at Hung.none returns seven
chains: the key file's three written ones, the entry's chain, the proof file's three written ones.
The last term: Johnson/AtFull/Sends/SendsW.lean's `sends_W` | `sends_all` at
`IM.keySendsFive_at_W` (Johnson/IMR/KeySendsFive.lean), which pays their one premise. Calls
alone.

  `keySends_W`: KeySendsAtW IM.keyW IM.keyShared keySendsFull.1 keySendsFull.2.1 keySendsFull.2.2.
  **`sendsWhole_W`**: ∃ En, sendsFrom W = .ok [keySendsFull.1, keySendsFull.2.1, keySendsFull.2.2,
  En, proofSendsFull.1, proofSendsFull.2.1, proofSendsFull.2.2].
  **`sendsWhole_all`**: ∃ En, ∀ c, freeOf c = writtenMade → sendsFrom c = the same list.

Limits. At the written parts; that a made record's four free parts are the written ones is a premise
of the second statement and is not said here. The entry's chain is shown to return; there is no
written chain to hold it against. That the written chains are what the C++ programs send
is not said. Nothing on soundness.
-/
import Johnson.AtFull.Sends.SendsW
import Johnson.IMR.KeySendsFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Sends

open VerifiableInference.PlanWritten VerifiableInference.PlanWritten.Joined Johnson.G
  Johnson.G.MadeFree
open OnBytes OnBytes.Params

/-- **The key file's five steps at the written parts**: `IM.keySendsFive_at_W`'s closed facts. -/
theorem keySends_W :
    KeySendsAtW IM.keyW IM.keyShared keySendsFull.1 keySendsFull.2.1 keySendsFull.2.2 :=
  ⟨IM.keySendsFive_at_W.1, IM.keySendsFive_at_W.2.1, IM.keySendsFive_at_W.2.2.1,
    IM.keySendsFive_at_W.2.2.2.1, IM.keySendsFive_at_W.2.2.2.2⟩

/-- **The sendings as a value at the written parts: no premise.** -/
theorem sendsWhole_W : ∃ En, sendsFrom W = .ok [keySendsFull.1, keySendsFull.2.1, keySendsFull.2.2,
    En, proofSendsFull.1, proofSendsFull.2.1, proofSendsFull.2.2] := sends_W keySends_W

/-- **One En for every record whose four free parts are the written ones.** -/
theorem sendsWhole_all : ∃ En, ∀ c : Configured, freeOf c = writtenMade →
    sendsFrom c = .ok [keySendsFull.1, keySendsFull.2.1, keySendsFull.2.2, En, proofSendsFull.1,
      proofSendsFull.2.1, proofSendsFull.2.2] := sends_all keySends_W

end Johnson.AtFull.Sends

#print axioms Johnson.AtFull.Sends.keySends_W
#print axioms Johnson.AtFull.Sends.sendsWhole_W
#print axioms Johnson.AtFull.Sends.sendsWhole_all
