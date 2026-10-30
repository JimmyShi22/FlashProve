-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/BordersPlan.lean: ONE TEST, WITH CODE, ON THE TABLE OF JOINTS' LETTERS ON THE
PLAN's
SIDE: the numbers (`Numbers`, Borders.lean), arr, the members' lists (`MemberLists`,
Johnson/Desc/PlanMem.lean) and the description. It imports Borders.lean and PlanMem.lean alone.
NOTHING IS PROVED IN THIS FILE.
  `laysOpen`: at every row that lays, the pins of the row's own seats are open in front of its
    block.
  `laysAreMembers`: every seat that a row lays is a member's.
  `baseOf F k`: how many trees the first chain's blocks in front of block number k tell.
  `groupsAreMembers`: every seat of every group, the index masks' and W's is a member's.
  `planSideOk F codes L arr N links ps`: ALL TOGETHER: the index fits the chain (`placesFit`) · the
    numbers fit the description's own oracles (`numbersFit`) · no member has a fault (`seatsFitB`) ·
    no two members have one seat · `laysAreMembers` · `laysNodup` · `laysFenced` at `baseOf` ·
    `laysOpen` · `laysClear` · `laysAll` · `padsOnce` · members with one number have their pads at
    one place (`padSame`, PlanMem.lean) · `oneAnswer` · `groupsAreMembers`.
What a yes gives: Johnson/Desc/Sound/BordersPlanProofs.lean [not in this library].
Limits. A yes says nothing on whether the lists, the numbers and arr are the plan's: they are
handed in. `laysClear` tests the table's own word on which tenants an item reads.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.PlanMem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- At every row that lays, the pins of the row's own seats, and of the seats whose pads alone it
lays, are open in front of its block. O: the items that are open at each border, from the chain's
first. -/
def laysOpen (N : Numbers) (links : List ModelPart) (ps : List Place) (O : List (List Item)) : Bool :=
  ps.zipIdx.all fun q =>
    (laysSeats N links q.1 ++ laysPads N links q.1).all fun x =>
      (sampledIn N (O[q.2]?.getD [])).contains x

/-- Every seat that a row lays, whole or the pad alone, is a member's. -/
def laysAreMembers (N : Numbers) (links : List ModelPart) (ps : List Place) (L : MemberLists) : Bool :=
  ps.all fun p => (laysSeats N links p ++ laysPads N links p).all (allSeats L).contains

/-- Every seat of every group, the index masks' and W's is a member's. n: the number of segments. -/
def groupsAreMembers (N : Numbers) (n : Nat) (L : MemberLists) : Bool :=
  ((List.range (n + 1)).flatMap N.group ++ [N.index, N.w]).all (allSeats L).contains

/-- How many trees the first chain's blocks in front of block number k tell. -/
def baseOf {Xi : Type} (F : FileDescription Xi) (k : Nat) : Nat := (oraclesOf (F.first.blocksInOrder.take k)).length

/-- **The plan's side of the table, as one test.** -/
def planSideOk {Xi : Type} (F : FileDescription Xi) (codes : OnBytes.Codes) (L : MemberLists)
    (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) (ps : List Place) : Bool :=
  placesFit F.first ps && numbersFit (oraclesOf F.first.blocksInOrder) N links.length &&
    seatsFitB F codes L && eachOnce (allSeats L) && laysAreMembers N links ps L &&
    laysNodup arr N links ps && laysFenced (baseOf F) N links ps &&
    laysOpen N links ps (openSets links ps (start links)) &&
    laysClear arr N links ps (start links) && laysAll arr N links ps &&
    padsOnce arr N links ps && VerifiableInference.Desc.padSame codes L arr && oneAnswer L &&
    groupsAreMembers N links.length L

end VerifiableInference.Desc.First
