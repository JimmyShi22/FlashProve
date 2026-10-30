-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/ReadsFit.lean: WHAT THE LAYERS OF THE TABLE OF JOINTS' FILLING SAY THAT THEIR
SENTENCES READ OF THE WITNESS, HELD AGAINST WHAT THE TABLE BOOKS: a test with code. No Mathlib.

Why. The table books, item by item, through which components a sentence may read the witness
(`Item.reads`, Johnson/Desc/First/Borders.lean). Whether the sentences that are laid in read no more
was held by readers' eyes alone, and arms were found lacking one by one.
  R : Item → List Comp: WHAT THE SENTENCE AT AN ITEM READS, BY ITS AUTHORS' OWN WORD: MEANT: each
  layer
    names it for the items whose field it lays, and proves that its sentence reads the witness
    through
    that list alone (`ReadsAt`, Johnson/Desc/Sound/ReadsFitLaw.lean, where one layer does so).
  `readsFitAt arr N links R i`: every component of R i is booked by the table at i.
  `readsFit arr N links R items`: so at every item of a list.
  `lacking arr N links R items`: for a print: the items at which it is not so, each with the
    components that the table does not book.
  `openItems links ps`: the items that are open at any border of the table's index, each once.
  `readsFit_mem`: the test's yes, item by item and component by component.
Limits: the test holds WORDS against the table: that a layer's R is true of its sentence is that
layer's lemma. Nothing on soundness.

-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- Every component that the sentence at i is said to read is booked by the table at i. -/
def readsFitAt (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) (R : Item → List Comp)
    (i : Item) : Bool :=
  (R i).all fun c => (i.reads arr N links).contains c

/-- So at every item of a list. -/
def readsFit (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) (R : Item → List Comp)
    (items : List Item) : Bool :=
  items.all fun i => readsFitAt arr N links R i

/-- For a print: where it is not so, and what lacks. -/
def lacking (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) (R : Item → List Comp)
    (items : List Item) : List (Item × List Comp) :=
  items.filterMap fun i =>
    let l := (R i).filter fun c => !(i.reads arr N links).contains c
    if l.isEmpty then none else some (i, l)

/-- The items that are open at any border, each once. -/
def openItems (links : List ModelPart) (ps : List Place) : List Item :=
  ((openSets links ps (start links)).flatMap id).eraseDups

theorem readsFit_mem (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart)
    (R : Item → List Comp) (items : List Item) (h : readsFit arr N links R items = true)
    (i : Item) (hi : i ∈ items) (c : Comp) (hc : c ∈ R i) : c ∈ i.reads arr N links := by
  have h1 := List.all_eq_true.1 h i hi
  have h2 := List.all_eq_true.1 h1 c hc
  simpa using h2

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.readsFit_mem
