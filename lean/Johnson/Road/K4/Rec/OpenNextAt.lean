-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/OpenNextAt.lean: THE TEST `openNextB`
(Johnson/Road/K4/Rec/NextEntryStatement.lean:
"the promise asks the four public items at border j") AT EVERY PLACE OF K4's
SUB-PROTOCOL, AS ONE TEST WITH A LAW, GENERAL IN THE LIST OF EXTRA PUBLIC TESTS M; AND WHAT LEAN's
KERNEL SAYS AT THE WRITTEN LIST OF 25 SEGMENTS OF THE HALF THAT READS NO M. Definitions with code,
two laws, evaluated statements.

  `k4OpenNextFit M links ps`: `openNextB M links ps (k + 1) m` at every place of K4's (border k in
    front of it, segment m).
  `openNext_of_fit`: where it accepts, `openNextB M links ps (k + 1) m = true` at each such place:
    the field openNext of the structure K4NameAt (Johnson/Road/K4/K04LawOf.lean), to the letter.
    Premises: H (in the caller's hand) · the test's accept (evaluated at one M, the wider meaning's
    list `moreWideAll`: `k4_openNext_wide`, Johnson/Road/K4/Rec/OpenNextWide.lean).
  `indexIs_held`: where the item pinI is open at border j, the promise asks indexIs there, at
    every M.
  `k4PinIFit links ps`: pinI is open at the border behind K4's sub-protocol, at every place of
    K4's.
  **`k4_pinI_full`**: BY THE KERNEL: true at the written list, which has twelve places of K4's (the
    count is part of the statement).
  `pinI_closed_at_start`: at border 0, in front of the sub-protocol that opens pinI: false. No
    control: it cannot fail: that border's set is `start links`, which never holds pinI.
  `indexIs_in_no_set`: THE KERNEL's WORD ON WHY THE TEST DOES NOT ASK IN `pubSets` ALONE, at one M
    (the composed meaning's list before the names that leave are struck, `moreUnstruck`,
    Johnson/Desc/Sound/MoreAll.lean): at none of the borders does `pubSets` hold indexIs. So a
    test that asks it there rejects at each of them.
Limits. THREE OF THE FOUR ITEMS ARE NAMES OF EXTRA PUBLIC TESTS ("K12.msgShapes", "K13.pileWithin",
"pile.room"): whether they are open behind K4's sub-protocol hangs on M: `k4OpenNextFit` HAS BEEN
EVALUATED AT ONE M, the wider meaning's list `moreWideAll`, where it accepts (`k4_openNext_wide`,
Johnson/Road/K4/Rec/OpenNextWide.lean). At the composed meaning's own list `moreAll` the three are
struck: there the test must reject (by reading): it can be met at a wider meaning alone. THE LIST OF
SEGMENTS IS WRITTEN (`linksFull`, Johnson/Desc/Sound/AtDriver.lean), not read off the public
parameters. That `pubSets` holds indexIs at NO M is read off the table's text, not proved. K04_law,
the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Rec.NextEntryStatement
import Johnson.Road.K4.Riders.PlanTests
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.MoreAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open OnBytes.Road.K4.Riders (atK4s atK4s_at)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item Pub More start openSets pubSets pubOfItems
  flatPlacesOf)
open VerifiableInference.Desc.First.FillK4 (isK4At)
open VerifiableInference.Desc.Sound (linksFull moreUnstruck)

variable {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- The promise asks the four items behind K4's sub-protocol, at every place of K4's. -/
def k4OpenNextFit (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k m => openNextB M links ps (k + 1) m

/-- What an accept gives at a place of K4's. -/
theorem openNext_of_fit {M : More} (H : AtK4 links ps k m pl)
    (h : k4OpenNextFit M links ps = true) : openNextB M links ps (k + 1) m = true :=
  atK4s_at (t := fun k m => openNextB M links ps (k + 1) m) H h

/-- Where pinI is open, the promise asks indexIs. -/
theorem indexIs_held (M : More) {j : ℕ}
    (h : Item.pinI ∈ (openSets links ps (start links))[j]?.getD []) :
    Pub.indexIs ∈ heldAt M links ps j := by
  unfold heldAt pubOfItems
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨.pinI, h, List.Mem.head _⟩)

/-- pinI is open behind K4's sub-protocol, at every place of K4's. -/
def k4PinIFit (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k _ => decide (Item.pinI ∈ (openSets links ps (start links))[k + 1]?.getD [])

/-- What an accept gives at a place of K4's. -/
theorem pinI_of_fit (H : AtK4 links ps k m pl) (h : k4PinIFit links ps = true) :
    Item.pinI ∈ (openSets links ps (start links))[k + 1]?.getD [] :=
  of_decide_eq_true (atK4s_at H h)

set_option maxRecDepth 1000000 in
theorem k4_pinI_full :
    (k4PinIFit linksFull (flatPlacesOf linksFull true) &&
      ((flatPlacesOf linksFull true).countP (isK4At linksFull) == 12)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A closed fact, no control**: at the first border pinI is not open. It cannot fail: that
border's set is `start links`, which holds pinI at no list of segments. -/
theorem pinI_closed_at_start :
    decide (Item.pinI ∈
      (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[0]?.getD []) =
      false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Why `openNextB` does not ask in `pubSets` alone, at one list of extra public tests**: no
border's set holds indexIs: a test that asks it there rejects. -/
theorem indexIs_in_no_set :
    ((pubSets moreUnstruck linksFull (flatPlacesOf linksFull true)).all fun Q =>
      !Q.contains .indexIs) = true := by
  decide +kernel

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.openNext_of_fit
#print axioms OnBytes.Road.K4.Rec.indexIs_held
#print axioms OnBytes.Road.K4.Rec.pinI_of_fit
#print axioms OnBytes.Road.K4.Rec.k4_pinI_full
#print axioms OnBytes.Road.K4.Rec.pinI_closed_at_start
#print axioms OnBytes.Road.K4.Rec.indexIs_in_no_set
