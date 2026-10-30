-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/PlusMoreWritten.lean: the five premises of the second form of the law on the
sub-protocol K13 that read a list of extra public tests (the binders hRowB, hIn, hQ, hD₀ and hD₁ of
`k13_law_topR` [not in this library]), at closed terms for all their arguments, each with a negative
test; and each in the
binder's own letters, wherever the composed filling's list is the closed one.

Row or tool. Two definitions, one equation by definition, closed facts, and laws by rewriting. They
are examples and payers for premises of another law. No law on a sub-protocol is named.

The arguments, their closed terms and their ties.
  `Mg₉.more`: `moreSpelt`, here: six tables merged, and the names that leave struck. It is the text,
    sign for sign, of `Sound.moreAll` (Johnson/Desc/Sound/MoreAll.lean), which `mgAll_more_closed`
    with `mgMore_is` (Johnson/Desc/Sound/MgAllAt.lean, MoreAll.lean) tie to the composed filling.
    These two files are not imported here: that `moreSpelt = Sound.moreAll` is one `rfl`:
    `moreSpelt_is` (Johnson/HB/LLHARD/OwedTies.lean).

    (Where this and lean/THEOREM.md differ, the page holds.) Here the equation `Mg₉.more =
    moreSpelt` is a premise of the laws by rewriting.
  `(plus13 D₁₃ d₁₂ Mg₉).more`: `plusMoreAll`. Tie: `plus13_more_at`, here. The three layers that
    `plus13` (Johnson/Desc/K13/Law/BridgeK13.lean) lays each merge their own tables over the list
    beneath: the letters D₁₃ and d₁₂ are not read.
  `cA13`, `Sound.linksFull`, `First.flatPlacesOf Sound.linksFull true`, 355 and 356: constants in
    the binders themselves. No tie is wanted. the items: the binders hIn and hQ name eight items.
    Four of the names (`pileMasksItem`, `pileWithinItem`, `oneRowItem`,
    Johnson/Desc/K13/Law/MasksDoor.lean) are used here. The other names stand here by their defining
    terms: `bookItem`, `seatsItem`, `shapesItem` are `moreItem nBook`, `moreItem nSeats`, `moreItem
    nShapes`; `weightsItem` and `bookFitsItem` are `moreItem (none, "K13.weightsOk")` and `moreItem
    (none, "K12.bookFits")`; `knownK13` is the list of the first three and `pileMasksItem`
    (FillFromSentences.lean, IndexSeatAtTable.lean, RidersK12.lean, FillM3Paid.lean,
    RidersMore.lean, MgK13.lean, all in Johnson/Desc/K13/Law/). By reading. The files that hold
    these names are not imported here.

What is here.
  `moreSpelt`. `plusMoreOf M`, `plusMoreAll`: seven tables merged over M; the same over `moreSpelt`.
    `plus13_more_is`: `(plus13 D d Mg).more = plusMoreOf Mg.more`, by definition. `plus13_more_at`.
  `rowPlus_written`, `rowPlus_rejects`: `rowM3B` at `plusMoreAll` accepts at 355; it rejects at 354,
    at 356, and at 355 with one more item made at K13's own place.
  `inPlus_written`, `inPlus_rejects`: the three items on the book, the seats and the shapes are open
    at border 355 at `plusMoreAll`; at `moreSpelt`, from which their names are struck, none is.
  `allPlus_written`, `allPlus_rejects`: every item that is open there is one of the eight that the
    binder hQ lists; with one more item open from the start, not every one is.
  `doors_written`, `doors_rejects`: `doorsFitB moreSpelt plusMoreAll cA13` accepts at 355 and at
    356; with the two lists exchanged, and with an empty class, it rejects.
  `hRowB_at`, `hIn_at`, `hQ_at`, `hD_at`: the five binders from `Mg₉.more = moreSpelt`: hRowB, hD₀
    and hD₁ to the letter; hIn and hQ with the items' defining terms in the place of five names and
    one list. By rewriting; nothing is evaluated.
By evaluations in Lean's kernel (`decide +kernel`): the eight facts with `written` or `rejects` in
their names.

Limits. By the head of AtTableRow.lean no negative test reaches clauses 3, 4, 5, 7 and 9 of `rowM3B`
alone; none does here. Nothing on soundness.


-/
import Johnson.Desc.K13.Law.BridgeK13
import Johnson.Desc.K13.Law.AtTableRow
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.Close.Law.FillRowFirst
import Johnson.Desc.First.FillBare
import Johnson.Desc.First.FillSentLater
import Johnson.Desc.First.FillSent
import Johnson.Desc.First.Att.Door.Door
import Johnson.Desc.K13.Law.SitsDoor
import Johnson.Desc.First.SmallDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open VerifiableInference.Desc.First (More Meaning Pub flatPlacesOf pubSets weightsMore moreItem)
open VerifiableInference.Desc.K12.Door (K12Data k12More shapesMore nBook nSeats nShapes)
open VerifiableInference.Desc.Sound (linksFull doorsFitB)
open VerifiableInference.Desc.First (rowMore leavesName)
open VerifiableInference.Desc.First.FillSent (sentMore sent1More)
open VerifiableInference.Desc.First.FillBare (leftMore)

/-- **The composed filling's closed list of extra public tests, spelled out of its six tables.** -/
def moreSpelt : More :=
  (((((((({} : More).merge rowMore).merge leftMore).merge sent1More).merge sentMore).merge
    H2K5.Door.more).merge wSitsMore).strike leavesName)

/-- Seven tables merged over a list of extra public tests. -/
def plusMoreOf (M : More) : More :=
  ((M.merge (k12More.merge shapesMore)).merge weightsMore).merge
    (k13Asks.merge (pileMasksMore.merge (pileWithinMore.merge oneRowMore)))

/-- **The wider list, closed.** -/
def plusMoreAll : More := plusMoreOf moreSpelt

section
variable {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (d : K12Data) (Mg : Meaning Pp W)

/-- **The three layers read neither D nor d in this field.** -/
theorem plus13_more_is : (plus13 D d Mg).more = plusMoreOf Mg.more := rfl

theorem plus13_more_at (h : Mg.more = moreSpelt) : (plus13 D d Mg).more = plusMoreAll := by
  rw [plus13_more_is, h]
  rfl

end

/-! ## hRowB -/

set_option maxRecDepth 1000000 in
theorem rowPlus_written :
    rowM3B plusMoreAll linksFull (flatPlacesOf linksFull true) 355 = true := by decide +kernel

/-- One more item, made at K13's own place. -/
def madeAt13 : More where
  rows := fun _ p => if p.kind == .K13 then { makes := [(none, "a negative test")] } else {}

set_option maxRecDepth 1000000 in
theorem rowPlus_rejects :
    rowM3B plusMoreAll linksFull (flatPlacesOf linksFull true) 354 = false ∧
      rowM3B plusMoreAll linksFull (flatPlacesOf linksFull true) 356 = false ∧
      rowM3B (plusMoreAll.merge madeAt13) linksFull (flatPlacesOf linksFull true) 355 = false := by
  decide +kernel

/-! ## hIn -/

set_option maxRecDepth 1000000 in
theorem inPlus_written :
    moreItem nBook ∈
        (pubSets plusMoreAll linksFull (flatPlacesOf linksFull true))[355]?.getD [] ∧
      moreItem nSeats ∈
        (pubSets plusMoreAll linksFull (flatPlacesOf linksFull true))[355]?.getD [] ∧
      moreItem nShapes ∈
        (pubSets plusMoreAll linksFull (flatPlacesOf linksFull true))[355]?.getD [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem inPlus_rejects :
    moreItem nBook ∉ (pubSets moreSpelt linksFull (flatPlacesOf linksFull true))[355]?.getD [] ∧
      moreItem nSeats ∉ (pubSets moreSpelt linksFull (flatPlacesOf linksFull true))[355]?.getD [] ∧
      moreItem nShapes ∉
        (pubSets moreSpelt linksFull (flatPlacesOf linksFull true))[355]?.getD [] := by
  decide +kernel

/-! ## hQ -/

set_option maxRecDepth 1000000 in
theorem allPlus_written :
    ∀ q ∈ (pubSets plusMoreAll linksFull (flatPlacesOf linksFull true))[355]?.getD [],
      q ∈ [moreItem nBook, moreItem nSeats, moreItem nShapes, pileMasksItem] ∨
        q = moreItem (none, "K13.weightsOk") ∨ q = pileWithinItem ∨ q = oneRowItem ∨
        q = moreItem (none, "K12.bookFits") := by
  decide +kernel

/-- One more item, open from the chain's start. -/
def openFromStart : More where
  start := [(none, "a negative test")]

set_option maxRecDepth 1000000 in
theorem allPlus_rejects :
    ¬ ∀ q ∈ (pubSets (plusMoreAll.merge openFromStart) linksFull
        (flatPlacesOf linksFull true))[355]?.getD [],
      q ∈ [moreItem nBook, moreItem nSeats, moreItem nShapes, pileMasksItem] ∨
        q = moreItem (none, "K13.weightsOk") ∨ q = pileWithinItem ∨ q = oneRowItem ∨
        q = moreItem (none, "K12.bookFits") := by
  decide +kernel

/-! ## hD₀ and hD₁ -/

set_option maxRecDepth 1000000 in
theorem doors_written :
    doorsFitB moreSpelt plusMoreAll cA13 linksFull (flatPlacesOf linksFull true) 355 = true ∧
      doorsFitB moreSpelt plusMoreAll cA13 linksFull (flatPlacesOf linksFull true) (355 + 1) =
        true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem doors_rejects :
    doorsFitB plusMoreAll moreSpelt cA13 linksFull (flatPlacesOf linksFull true) 355 = false ∧
      doorsFitB moreSpelt plusMoreAll (fun _ => false) linksFull (flatPlacesOf linksFull true) 355 =
        false := by
  decide +kernel

/-! ## The five binders, to the letter -/

section
variable {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (d : K12Data) {Mg : Meaning Pp W}

theorem hRowB_at (h : Mg.more = moreSpelt) :
    rowM3B (plus13 D d Mg).more linksFull (flatPlacesOf linksFull true) 355 = true := by
  rw [plus13_more_at D d Mg h]
  exact rowPlus_written

theorem hIn_at (h : Mg.more = moreSpelt) :
    moreItem nBook ∈ (pubSets (plus13 D d Mg).more linksFull
        (flatPlacesOf linksFull true))[355]?.getD [] ∧
      moreItem nSeats ∈ (pubSets (plus13 D d Mg).more linksFull
        (flatPlacesOf linksFull true))[355]?.getD [] ∧
      moreItem nShapes ∈ (pubSets (plus13 D d Mg).more linksFull
        (flatPlacesOf linksFull true))[355]?.getD [] := by
  rw [plus13_more_at D d Mg h]
  exact inPlus_written

theorem hQ_at (h : Mg.more = moreSpelt) :
    ∀ q ∈ (pubSets (plus13 D d Mg).more linksFull (flatPlacesOf linksFull true))[355]?.getD [],
      q ∈ [moreItem nBook, moreItem nSeats, moreItem nShapes, pileMasksItem] ∨
        q = moreItem (none, "K13.weightsOk") ∨ q = pileWithinItem ∨ q = oneRowItem ∨
        q = moreItem (none, "K12.bookFits") := by
  rw [plus13_more_at D d Mg h]
  exact allPlus_written

theorem hD_at (h : Mg.more = moreSpelt) :
    doorsFitB Mg.more (plus13 D d Mg).more cA13 linksFull (flatPlacesOf linksFull true) 355 =
        true ∧
      doorsFitB Mg.more (plus13 D d Mg).more cA13 linksFull (flatPlacesOf linksFull true)
        (355 + 1) = true := by
  rw [plus13_more_at D d Mg h, h]
  exact doors_written

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.plus13_more_is
#print axioms VerifiableInference.Desc.K13.Law.plus13_more_at
#print axioms VerifiableInference.Desc.K13.Law.rowPlus_written
#print axioms VerifiableInference.Desc.K13.Law.rowPlus_rejects
#print axioms VerifiableInference.Desc.K13.Law.inPlus_written
#print axioms VerifiableInference.Desc.K13.Law.inPlus_rejects
#print axioms VerifiableInference.Desc.K13.Law.allPlus_written
#print axioms VerifiableInference.Desc.K13.Law.allPlus_rejects
#print axioms VerifiableInference.Desc.K13.Law.doors_written
#print axioms VerifiableInference.Desc.K13.Law.doors_rejects
#print axioms VerifiableInference.Desc.K13.Law.hRowB_at
#print axioms VerifiableInference.Desc.K13.Law.hIn_at
#print axioms VerifiableInference.Desc.K13.Law.hQ_at
#print axioms VerifiableInference.Desc.K13.Law.hD_at
