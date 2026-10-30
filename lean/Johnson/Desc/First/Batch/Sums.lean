-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Sums.lean (kind K9): DEFINITIONS WITH CODE; NO THEOREM: the test on a
segment's sums that is K9's: EVERY SENT SCALAR STANDS IN A CLAIM. When all claims have been added,
the ledger holds for each slot its coefficient in the one equation. For each of the first n slots,
those that the segment's messages fill, the coefficient must be other than 0; but at the slot of the
merge's end value, if the segment has one, it must be 0: no claim of this segment says what that
value is; the row on the committed weights does.
A coefficient is a sum of products of drawn elements: an unlucky challenge can make it 0: the run is
refused then too. The program `verify-on-bytes` asks this in three places, in three forms: at a
feed-forward segment it marks the state as failed and goes on; at an attention segment and at the
head's it refuses at once, and skips the test in its dry run. Here it is always asked, and refuses
at once. It is called by the block of the tests behind the adding
(Johnson/Desc/First/Batch/Tests.lean). The condition is that of freeSlotOk
(Johnson/Desc/First/Door/Sums.lean), under K9's name for the refusal.


-/
import Johnson.Desc.First.Batch.Text

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- n: the slots that the segment's messages fill. merge: the slot of the merge's end value. -/
def freeSlot (n : Nat) (merge : Option Nat) (F : Fork) : Ans Unit :=
  need "K9.free-slot" ((List.range n).all fun j => isZeroE (F.LS.getD j zeroE) == (merge == some j))

end VerifiableInference.Desc.K9
