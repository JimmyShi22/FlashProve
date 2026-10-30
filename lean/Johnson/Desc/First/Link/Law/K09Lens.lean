-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K09Lens.lean: TWO LENGTHS, BY THE KERNEL, ON WHICH THE COUNTS «100
places» AND «25 shuttings» OF K09Closed.lean HANG: the list `P5J.fullLinks` has 25 members; its
list of places has 358: so the tests there range over 25 links, and the greatest number that they
ask (347 + 4) lies inside the list. Evaluations.

What is said.
  `links_25`, `places_358`: the two lengths. `asked_inside`: every number that K09Closed.lean's
    tests ask at the offsets 0 to 4 lies inside the list of places.

Limits. Closed facts on the written list. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K09Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (flatPlacesOf)

set_option maxRecDepth 1000000

theorem links_25 : P5J.fullLinks.length = 25 := by decide +kernel

theorem places_358 : (flatPlacesOf P5J.fullLinks true).length = 358 := by decide +kernel

/-- Every number asked lies inside the list. -/
theorem asked_inside : ((List.range P5J.fullLinks.length).all fun m =>
    decide (batchAt P5J.fullLinks (flatPlacesOf P5J.fullLinks true) m + 4 <
      (flatPlacesOf P5J.fullLinks true).length)) = true := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.links_25
#print axioms VerifiableInference.Desc.LinkJoin.places_358
#print axioms VerifiableInference.Desc.LinkJoin.asked_inside
