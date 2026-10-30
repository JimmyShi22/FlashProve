-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlacesCount.lean: the kind "the code switch" (K2): THE TWO
CLOSED LISTS ARE NOT EMPTY: the written list of the kind's places (`placesW`) has 25 members and the
written list of segments (`segsW`) has 25 (both: Honest/K2/Law/PlacesWritten.lean). Statements with
their proofs; no definition. The three counts are closed facts: `decide +kernel` under a raised
recursion depth. No head, no state, no prover.

  `placesW_count` the list of places has 25 members
  `placesW_one` at each place `switchPlaceAt l` (Johnson/Desc/K2/Honest/Returns/SeatAtLinks.lean), l
                    from 1 to 23, just one of them
  `placesW_border` CONTROL for that: at `switchPlaceAt 24` none: so the range 1 to 23 is not for
                    nothing
  `segsW_count` the list of segments has 25 members
  `placesAt_none` with `segsAt_none`: WHY A COUNT IS WANTED AT ALL: where the preparation is wanting
                    both bodies are the empty list: a sentence "at all members" of such a list would
                    hold for want of a case; the counts shut that out at the written lists

WHY A FILE OF ITS OWN. A law of the form "all members of `placesW` …", or "no member …", is true of
an empty list. Whoever states one can call the count beside it. Honest/K2/Law/PublicAtWritten.lean,
a file of tests at these 25 places, imports this file for the first two.

Kin, not called. `fencesW` (Honest/K2/Law/TiesWritten.lean): one closed fact, a conjunction of five
counts, WHOSE FIRST TWO MEMBERS ARE `placesW_count` AND `segsW_count`: so the second is no new
matter: it has a name and a home of its own here. A NAMESAKE: the library's `IM.places_len :
placesW.length = 358` (Johnson/IMR/WrittenList.lean) speaks of another `placesW`, `IM.placesW`: a
list of `Place`: the places of all blocks of the first chain (`flatPlacesOf`,
Johnson/Desc/First/Driver/Chain.lean).

Limits. At the written plan alone: the full size, the format's second hash function. That the plan's own
lists are these under the head is `places_at_head` and `segments_at_head` (PlacesWritten.lean).
Lean's kernel has evaluated the three counts and the border; no independent checker has replayed
them. Nothing on what a place or a segment holds. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.K2.Honest.Returns.SeatAtLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest.Returns (switchPlaceAt)

set_option maxRecDepth 1000000 in
/-- The written list of the kind's places has 25 members. -/
theorem placesW_count : placesW.length = 25 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At each of the links 1 to 23 just one. -/
theorem placesW_one : ((List.range 23).all fun i =>
    (placesW.filter fun p => p.place == switchPlaceAt (i + 1)).length == 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- CONTROL: at the next number none. -/
theorem placesW_border : (placesW.filter fun p => p.place == switchPlaceAt 24).length = 0 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written list of segments has 25 members. -/
theorem segsW_count : segsW.length = 25 := by decide +kernel

/-- Why a count is wanted: without a preparation there is no place. -/
theorem placesAt_none (sps? : Option (List Spot)) : placesAt none sps? = [] := by
  cases sps? <;> rfl

/-- Nor a segment. -/
theorem segsAt_none (fold : List Nat) : segsAt none fold = [] := rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.placesW_count
#print axioms ProofFile.Honest.K2.Law.placesW_one
#print axioms ProofFile.Honest.K2.Law.placesW_border
#print axioms ProofFile.Honest.K2.Law.segsW_count
#print axioms ProofFile.Honest.K2.Law.placesAt_none
#print axioms ProofFile.Honest.K2.Law.segsAt_none
