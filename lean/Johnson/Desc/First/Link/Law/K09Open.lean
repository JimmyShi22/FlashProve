-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K09Open.lean: A CLOSED FACT ON THE WRITTEN LIST THAT THE ONE EQUATION's
THIRD TIE TAKES: behind the one equation's place the item «the segment's row of the class equation»
is open: AS A BOOL, WITH THE KERNEL's YES AT THE LIST `P5J.fullLinks`. A definition, theorems,
evaluations.

What is said.
  `rowOpenFit links pl`: the Bool, at every link. `rowOpen_at`: **under its yes: the item is open at
    the border behind link m's one equation.** `rowOpenFit_links`: the kernel's yes at
    `P5J.fullLinks` and its list of places. `rowOpenFit_bent`: a negative test: with the first
    link's one equation and the sub-protocol behind it changed over in the list of places: no.

Limits. A closed fact on the written list. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K09Cond
import Johnson.Desc.First.Link.Law.RowsPush

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item flatPlacesOf start openSets)

/-- Behind each link's one equation the row's item is open. -/
def rowOpenFit (links : List ModelPart) (pl : List Place) : Bool :=
  (List.range links.length).all fun m => decide (Item.row m .equation ∈
    (openSets links pl (start links))[batchAt links pl m + 1 + 1 + 1]?.getD [])

/-- **UNDER THE BOOL's YES.** -/
theorem rowOpen_at (links : List ModelPart) (pl : List Place) (h : rowOpenFit links pl = true) (m : ℕ)
    (hm : m < links.length) : Item.row m .equation ∈
      (openSets links pl (start links))[batchAt links pl m + 1 + 1 + 1]?.getD [] :=
  of_decide_eq_true (List.all_eq_true.1 h m (List.mem_range.2 hm))

set_option maxRecDepth 1000000 in
/-- **THE KERNEL's YES AT THE LIST `P5J.fullLinks`.** -/
theorem rowOpenFit_links :
    rowOpenFit P5J.fullLinks (flatPlacesOf P5J.fullLinks true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: numbers 11 and 12 of the list changed over. -/
theorem rowOpenFit_bent :
    rowOpenFit P5J.fullLinks (swapAt (flatPlacesOf P5J.fullLinks true) 11) = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowOpen_at
#print axioms VerifiableInference.Desc.LinkJoin.rowOpenFit_links
#print axioms VerifiableInference.Desc.LinkJoin.rowOpenFit_bent
