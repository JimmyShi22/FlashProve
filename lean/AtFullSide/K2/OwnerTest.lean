-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/OwnerTest.lean: the kind "the code switch" (K2): ONE PUBLIC TEST AT A WRITTEN PLACE OF
THE KIND AND A LIST OF TUPLES (spender, start, count, mark): what AtFullSide/K2/BookBridge.lean's
law `book_at_owner` asks of written values, at the place's own codes, sending and fresh mask. Three
definitions with code; one small closed fact by evaluation in Lean's kernel, with a control. THE
TEST IS EVALUATED IN THE FILES AtFullSide/K2/OwnerTest/G01.lean … G11.lean, one owner a file, so
that each evaluation is let go before the next, and bent in OwnerTest/Bent.lean. It lies in the side
library because it imports files of it.

  `evenLink`        a place's link is one of 2, 4, …, 22
  `ownerTestAt`     THE TEST at a place p and a list, g := half p's link: p's place is the written
                    owner's · each spender's place in the list stands where the written positions
                    name it · the one test `ownerOk` (Johnson/Desc/ProofFile/Honest/K2/Law/
                    BookByRuns.lean) at p's own codes, sending and fresh mask, these positions, the
                    list
  `ownerTest`       the test at the written list of ALL entries of the place's owner
                    (`ownedListW`, AtFullSide/K1/RowTakers/AllDefs.lean, of other authors)
  `evenCountW`      BY LEAN's KERNEL: eleven written places have such a link, no two of them one
                    link; a control: the written places are more than eleven, so some of them fail
                    the test on the link. `evenLink` itself has no bent twin

Limits. DEFINITIONS AND A COUNT: the test is shown of no place here. Public: no coin occurs: starts
and counts are numbers. The full size alone. Nothing on any property.
-/
import AtFullSide.K1.RowTakers.AllDefs
import AtFullSide.K14.RawTwinKit
import Johnson.Desc.ProofFile.Honest.K2.Law.BookByRuns
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K2
open ProofFile.Honest.K2.Law (placesW ownerOk)
open P2Law.ProofPlan (WP)
open AtFullSide.K14 (posW)
open AtFullSide.K1 (ownerAt ownedListW)

/-- A place's link is one of 2, 4, …, 22. -/
def evenLink (p : SwitchPlace) : Bool :=
  p.link % 2 == 0 && decide (2 ≤ p.link) && decide (p.link ≤ 22)

/-- **THE TEST** at a place and a list of tuples. -/
def ownerTestAt (p : SwitchPlace) (L : List (Addr × Due × Due × Bool)) : Bool :=
  p.place == (ownerAt (p.link / 2)).place &&
    (L.all fun t => placedAt posW (orderOf WP) t.1.place) &&
    ownerOk p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) (beforeG posW) L

/-- The test at the written list of all entries of the place's owner. -/
def ownerTest (p : SwitchPlace) : Bool := ownerTestAt p (ownedListW (p.link / 2))

set_option maxRecDepth 1000000 in
/-- **Eleven written places have such a link, no two of them one link**; a control: the written
places are more than eleven. -/
theorem evenCountW :
    ((placesW.filter evenLink).map (·.link)) = [2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] ∧
      decide (11 < placesW.length) = true := by
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.evenLink
#print axioms AtFullSide.K2.ownerTestAt
#print axioms AtFullSide.K2.ownerTest
#print axioms AtFullSide.K2.evenCountW
