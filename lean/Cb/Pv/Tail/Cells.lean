-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/Cells.lean: what the relation before the smallness test's round gives: one integer matrix
for each committed matrix.

`relIn` (Cb/Pv/Tail/Block.lean) says column by column that there are small cells. Here the columns
are put together.

Main names:
  `cells_of_relIn`: there are integers, one for each matrix, row of cells and column, each below
    twice the shift in absolute value, such that every committed symbol is the packing of its three
    cells and every committed read is the weighted sum of its column's cells.
  `relIn_of_cells`: the converse.

Limits: nothing here says that the integers are unique; `Alg.small_unique` (Alg/Range.lean) does,
under conditions on the radix and on the characteristic of the ring.

Terms: lean/GLOSSARY.md.

-/
import Cb.Pv.Tail.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail

variable {K : Type} [CommRing K] {s : Size} (Λ : Letters K s)

/-- The integers a are cells behind the committed messages. -/
def CellsOK (x : Λ.X) (msg : Λ.M) (a : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) : Prop :=
  (∀ μ c i, |a μ c i| < 2 * (s.beta : ℤ)) ∧
  (∀ μ c i', Λ.sym msg μ i' c = ((Alg.pack (s.rad : ℤ) (a μ c) i' : ℤ) : K)) ∧
  (∀ μ c r, Λ.tab msg μ r c = ∑ i, Λ.w x μ r i * ((a μ c i : ℤ) : K))

theorem cells_of_relIn {x : Λ.X} {msg : Λ.M} (h : relIn Λ x msg) : ∃ a, CellsOK Λ x msg a := by
  choose a h1 h2 h3 using h
  exact ⟨a, h1, h2, h3⟩

theorem relIn_of_cells {x : Λ.X} {msg : Λ.M} {a : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ}
    (h : CellsOK Λ x msg a) : relIn Λ x msg :=
  fun μ c => ⟨a μ c, h.1 μ c, h.2.1 μ c, h.2.2 μ c⟩

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.cells_of_relIn
#print axioms Cb.Pv.Tail.relIn_of_cells
