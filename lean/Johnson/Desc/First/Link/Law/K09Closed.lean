-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K09Closed.lean: THE TWO CLOSED CONJUNCTS OF THE BATCHING KIND's
CONDITION (`K9Cond`, K09Cond.lean), EVALUATED BY THE KERNEL AT THE LIST `P5J.fullLinks`, EACH WITH A
NEGATIVE LINE: (b) at the 100 places of the 25 links' batchings, the two places behind each and the
shuttings, the table's row lays nothing (so that the table's extractor is the identity there); (c)
at the 25 shuttings the row closes nothing and reads nothing. Definitions and evaluations.

What is said.
  `laysNoneAt links pl off`: at every link, at the place `off` behind its batching's, the row lays
    nothing (`laysNothingAt`, Johnson/Desc/Sound/ExtQAtId.lean). `laysNone_0`, `_1`, `_2`, `_4`: the
    kernel's yes at `P5J.fullLinks` and its list of places. `laysNone_3`: THE NEGATIVE LINE: at the
    place between the one equation and the shutting the same test says no. `rowsEmptyAt links pl
    off`: at every link, at that place, the row's lists of what it closes and of what it reads are
    empty. `rowsEmpty_4`: the kernel's yes at the shuttings. `rowsEmpty_2`: THE NEGATIVE LINE: at
    the one equations the same test says no. `numbers_links`: the batchings' numbers are 14 m + 9 at
    the first 24 links and 347 at the head's.

Limits. Closed facts on the written list. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K09Cond
import Johnson.Desc.Sound.ExtQAtId

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart flatPlacesOf)

/-- At every link, at the place off behind its batching's, the row lays nothing. -/
def laysNoneAt (links : List ModelPart) (pl : List Place) (off : ℕ) : Bool :=
  (List.range links.length).all fun m => laysNothingAt links pl (batchAt links pl m + off)

/-- At every link, at that place, the row closes nothing and reads nothing. -/
def rowsEmptyAt (links : List ModelPart) (pl : List Place) (off : ℕ) : Bool :=
  (List.range links.length).all fun m =>
    decide ((rowQ links pl (batchAt links pl m + off)).ins = []) &&
    decide ((rowQ links pl (batchAt links pl m + off)).ctx = [])

set_option maxRecDepth 1000000

/-- **(b): THE KERNEL's YES AT THE 100 PLACES.** -/
theorem laysNone_0 : laysNoneAt P5J.fullLinks (flatPlacesOf P5J.fullLinks true) 0 = true := by
  decide +kernel

theorem laysNone_1 : laysNoneAt P5J.fullLinks (flatPlacesOf P5J.fullLinks true) 1 = true := by
  decide +kernel

theorem laysNone_2 : laysNoneAt P5J.fullLinks (flatPlacesOf P5J.fullLinks true) 2 = true := by
  decide +kernel

theorem laysNone_4 : laysNoneAt P5J.fullLinks (flatPlacesOf P5J.fullLinks true) 4 = true := by
  decide +kernel

/-- **(b): THE NEGATIVE LINE**: asked of the places between the one equations and the shuttings the
same test says no (at one link or more the row lays something). -/
theorem laysNone_3 : laysNoneAt P5J.fullLinks (flatPlacesOf P5J.fullLinks true) 3 = false := by
  decide +kernel

/-- **(c): THE KERNEL's YES AT THE 25 SHUTTINGS.** -/
theorem rowsEmpty_4 : rowsEmptyAt P5J.fullLinks (flatPlacesOf P5J.fullLinks true) 4 = true := by
  decide +kernel

/-- **(c): THE NEGATIVE LINE**: asked of the one equations' places the same test says no (at one
link or more a list is not empty). -/
theorem rowsEmpty_2 : rowsEmptyAt P5J.fullLinks (flatPlacesOf P5J.fullLinks true) 2 = false := by
  decide +kernel

/-- The batchings' numbers. -/
theorem numbers_links :
    (List.range 25).map (batchAt P5J.fullLinks (flatPlacesOf P5J.fullLinks true)) =
      (List.range 24).map (fun m => 14 * m + 9) ++ [347] := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.laysNone_0
#print axioms VerifiableInference.Desc.LinkJoin.laysNone_1
#print axioms VerifiableInference.Desc.LinkJoin.laysNone_2
#print axioms VerifiableInference.Desc.LinkJoin.laysNone_4
#print axioms VerifiableInference.Desc.LinkJoin.laysNone_3
#print axioms VerifiableInference.Desc.LinkJoin.rowsEmpty_4
#print axioms VerifiableInference.Desc.LinkJoin.rowsEmpty_2
#print axioms VerifiableInference.Desc.LinkJoin.numbers_links
