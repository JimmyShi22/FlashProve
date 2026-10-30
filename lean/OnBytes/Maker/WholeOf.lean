-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WholeOf.lean: the data of OnBytes/Maker/Whole.lean's reduction from the three chains
of a file as plain data (OnBytes/Three/Data.lean, `Whole`). Definitions alone.

  `rdtOf`: a round's data, field for field.
  `WholeD.of`: the first chain without its seal (`Whole.stretch₁`), the second, the third; the keys
    are `Whole.key`'s. The stored table's depth a is the caller's letter, so that the reductions of
    a key file, an entry file and a proof file can stand over strings of one length by their types.
  `storedFit`: a test: the first and the third chain open no stored table; every stored table that
    the second opens has the depth a and stands under the statement's item 0.
  `countsFit`: a test: the numbers of trees of the first two chains, which the reduction counts in
    its own lists of rounds, are those that W counts in the rounds as stated (the seal sends no
    root).
  `WholeD.workFit`: a test on the reduction's data: no round has more than 64 bits of work (what the
    laws of a wire record ask: OnBytes/Maker/WireLaws.lean).
  `WholeD.depthFit`: a test on the reduction's data: no tree that a round sends is deeper than 63.
  `WholeD.runFit`: a test on the reduction's data: no tree that a round sends bears the mark
    "stored".

What is not claimed. No law is stated here. `WholeD.of` calls none of these tests: whoever lays a
and W owes all five (OnBytes/Maker/Files.lean, `okAt`, calls them).


-/
import OnBytes.Maker.Whole
import OnBytes.Three.Data

set_option autoImplicit false

namespace OnBytes.Maker

/-- A round's data, field for field. -/
def rdtOf (d : Three.RDL) : RDT := ⟨⟨d.entry, d.kind, d.items, d.trees, d.opens⟩, d.stored⟩

/-- The second chain alone opens a stored table, and each that it opens has the depth a and stands
under the item 0. -/
def storedFit (a : ℕ) (W : Three.Whole) : Bool :=
  (W.ds₁ ++ W.ds₃).all (·.stored.isEmpty) &&
    W.ds₂.all fun d => d.stored.all fun s => s.sh.a == a && s.item == 0

/-- **The data of a whole file.** a: the stored table's depth. -/
def WholeD.of (a : ℕ) (W : Three.Whole) : WholeD where
  a := a
  ds₁ := W.stretch₁.map rdtOf
  ds₂ := W.ds₂.map rdtOf
  ds₃ := W.ds₃.map rdtOf
  key₁ := W.key 0
  key₂ := W.key 1
  key₃ := W.key 2

/-- The numbers of trees that the data's first two lists of rounds send are those that W counts. -/
def countsFit (a : ℕ) (W : Three.Whole) : Bool :=
  (WholeD.of a W).t₁ == W.t₁ && (WholeD.of a W).t₂ == W.t₂

/-- Every round of the three chains has at most 64 bits of work. -/
def WholeD.workFit (D : WholeD) : Bool :=
  (D.ds₁ ++ (D.ds₂ ++ D.ds₃)).all fun d => decide (d.entry.work ≤ 64)

/-- No tree that the three chains send is deeper than 63. -/
def WholeD.depthFit (D : WholeD) : Bool :=
  (D.ds₁ ++ (D.ds₂ ++ D.ds₃)).all fun d => d.trees.all fun s => decide (s.a ≤ 63)

/-- No tree that the three chains send bears the mark "stored". -/
def WholeD.runFit (D : WholeD) : Bool :=
  (D.ds₁ ++ (D.ds₂ ++ D.ds₃)).all fun d => d.trees.all fun s => !s.stored

end OnBytes.Maker
