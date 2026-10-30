-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/OwnerTest/G08.lean: the kind "the code switch" (K2): ONE CLOSED FACT BY EVALUATION IN
LEAN's KERNEL: the public test `ownerTest` (AtFullSide/K2/OwnerTest.lean) says yes at the written
place of the kind whose link is 16: at the written list of all entries of that place's owner. One of
eleven files of one form, one owner a file. That there is just one such place: `evenCountW`. That
the test can say no: OwnerTest/Bent.lean. No definition.

Limits. A FACT ON WRITTEN VALUES. The list is a listing: its authors printed it off the written
book's own entries, and Lean's kernel holds it against these
(AtFullSide/K1/OwnerEntriesAtSwitches.lean, not imported here). Public: no coin occurs. The full
size alone. Nothing on any property.
-/
import AtFullSide.K2.OwnerTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest.K2.Law (placesW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test says yes at the written place whose link is 16. -/
theorem ownerTestW08 : ((placesW.filter fun p => p.link == 16).all ownerTest) = true := by
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.ownerTestW08
