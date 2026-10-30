-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ViewTests.lean: two tests on the plain data of a file's three chains
(OnBytes/Three/Data.lean, `Whole`), which OnBytes/Maker/TypingViews.lean takes as hypotheses, and
one on a round of a description, which OnBytes/Maker/SmallTies.lean takes.
Definitions alone, so that a program can evaluate them.

  `WholeD.shape`: the shape of the tree with the number j over the whole file, as the rounds' data
    of OnBytes/Maker/Whole.lean have it.
  `shapesFit`: that shape is the one in the data's table, for every tree of the table.
  `sealBare`: the first chain has a last round, and that round opens nothing.
  `bareSeal`: a description's round is of the kind "sealed", has no item, and its entry asks for no
    position, element or matrix entry.

What is not claimed. No law is stated here. Nothing says that any data pass the tests.


-/
import OnBytes.Maker.WholeOf

set_option autoImplicit false

namespace OnBytes.Maker

/-- The shape of the tree with the number j over the whole file. -/
def WholeD.shape (D : WholeD) (j : ℕ) : Option Fmt.Shape :=
  if j < D.t₁ then treeShT D.ds₁ j
  else if j - D.t₁ < D.t₂ then treeShT D.ds₂ (j - D.t₁)
  else treeShT D.ds₃ (j - D.t₁ - D.t₂)

/-- A test: the shape of each tree in the rounds' data is the one in the data's table. -/
def shapesFit (a : ℕ) (W : Three.Whole) : Bool :=
  (List.range W.table.length).all fun j =>
    (WholeD.of a W).shape j == (W.table[j]?).map (·.shape)

/-- A test: the first chain has a last round, and that round opens nothing. -/
def sealBare (W : Three.Whole) : Bool :=
  match W.ds₁.getLast? with
  | none => false
  | some d => d.stored.isEmpty && d.opens.isEmpty

/-- A test on a description's round: it is of the kind "sealed", has no item, and its entry asks for
no position, element or matrix entry. -/
def bareSeal (x : Fmt.Round) : Bool :=
  x.kind == .sealed && x.items.isEmpty && x.entry.poss == 0 && x.entry.drawE == 0 &&
    x.entry.drawNZ == 0 && x.entry.trits == 0

end OnBytes.Maker
