--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/More/FrontList.lean: LEAN's KERNEL's WORD, AT THE FULL SIZE's WRITTEN LISTS AND THE
COMPOSED MEANING's OWN SMALL DOOR (`moreAll`): WHICH PUBLIC ITEMS ARE ASKED IN FRONT OF K4's
SUB-PROTOCOL: so that their tests can be drawn out of the promise's public test (`ePubAt`,
Johnson/Desc/First/EPubAt.lean). Definitions, statements and proofs: evaluation by the kernel.

  `frontOf`: ePubAt's own list at border k. `hasAtK4`: a test: at every place of K4's the item f m
    stands in that list.
  BY THE KERNEL, TRUE, A ROW AN ITEM: ledger · freeAbove · look · linkFresh · callerIn · lookOut m 2
    · "K4.lookLeft" · "K4.rowsBare" · "frame.sentIs" · "ledger.treesAre" · formsInT m 2 "objects".
  NEGATIVE TESTS, BY THE KERNEL, FALSE: "pile.room" · "frame.liveIs" of the segment ·
  "K12.seatsCarried" · "K12.msgShapes": THESE FOUR ARE NOT ASKED THERE AT THAT DOOR: whoever spends
  them in front of K4 has them from elsewhere.
  `front_mem`: what a yes gives at a place of K4's.

Limits. The table's book-keeping at two written lists. The full size alone. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Riders.PlanTests
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.First.EPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.More

open OnBytes.Road.K4.Riders (atK4s atK4s_at)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Pub More pubSets openSets start pubOfItems flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull moreAll)

/-- The list of the promise's public test at border k. -/
def frontOf (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : List Pub :=
  ((pubSets M links ps)[k]?.getD []) ++ pubOfItems ((openSets links ps (start links))[k]?.getD [])

/-- A test: at every place of K4's the item f m is asked in front. -/
def hasAtK4 (M : More) (links : List ModelPart) (ps : List Place) (f : ℕ → Pub) : Bool :=
  atK4s links ps fun k m => (frontOf M links ps k).contains (f m)

theorem front_mem {M : More} {links : List ModelPart} {ps : List Place} {f : ℕ → Pub} {k m : ℕ}
    {pl : Place} (H : AtK4 links ps k m pl) (h : hasAtK4 M links ps f = true) :
    f m ∈ frontOf M links ps k := by
  have h1 := atK4s_at H h
  simpa using h1

/-- The written list of places. -/
abbrev PS : List Place := flatPlacesOf linksFull true

set_option maxRecDepth 1000000 in
theorem has_ledger : hasAtK4 moreAll linksFull PS (fun m => .ledger m) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem has_freeAbove : hasAtK4 moreAll linksFull PS (fun m => .freeAbove m) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem has_look : hasAtK4 moreAll linksFull PS (fun m => .look m) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem has_linkFresh : hasAtK4 moreAll linksFull PS (fun m => .linkFresh m) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem has_callerIn : hasAtK4 moreAll linksFull PS (fun m => .callerIn m) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem has_lookOut : hasAtK4 moreAll linksFull PS (fun m => .lookOut m 2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem has_lookLeft :
    hasAtK4 moreAll linksFull PS (fun m => .more (some m) "K4.lookLeft") = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem has_rowsBare :
    hasAtK4 moreAll linksFull PS (fun m => .more (some m) "K4.rowsBare") = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem has_sentIs :
    hasAtK4 moreAll linksFull PS (fun m => .more (some m) "frame.sentIs") = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem has_treesAre :
    hasAtK4 moreAll linksFull PS (fun m => .more (some m) "ledger.treesAre") = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem has_objects :
    hasAtK4 moreAll linksFull PS (fun m => .formsInT m 2 "objects") = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem hasNot_room :
    hasAtK4 moreAll linksFull PS (fun m => .more (some m) "pile.room") = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem hasNot_liveIs :
    hasAtK4 moreAll linksFull PS (fun m => .more (some m) "frame.liveIs") = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem hasNot_seats :
    hasAtK4 moreAll linksFull PS (fun _ => .more none "K12.seatsCarried") = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem hasNot_shapes :
    hasAtK4 moreAll linksFull PS (fun _ => .more none "K12.msgShapes") = false := by
  decide +kernel

end OnBytes.Road.K4.More

#print axioms OnBytes.Road.K4.More.front_mem
#print axioms OnBytes.Road.K4.More.has_ledger
#print axioms OnBytes.Road.K4.More.has_objects
#print axioms OnBytes.Road.K4.More.hasNot_room
