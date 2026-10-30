-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Tail/Agree.lean: the relation before the smallness test's round gives: every committed read is
the value of a public linear form in the cells.

The statement has the form: for every entry j, u j = (a j).val m, with affine forms a
(`TWhole.Aff`, Cb/G6/Led.lean). Here m are the cells behind the committed symbols, as elements of
the field, u are the committed reads, and the form of a read at a column has the read's weights on
that column's cells and no constant.

Main names:
  `JCell s`: the cells: matrix, column, row. `affRead`: the form of a read at a column.
  `agree_of_cells`: cells behind the committed messages (`CellsOK`, Cb/Pv/Tail/Cells.lean) agree.
  `agree_of_relIn`: before the round there are integers, small, with the committed packing, whose
    images in the field agree with the committed reads.

Limits: the forms' coefficients come from the explicit statement before the round. The cells stand
under "there are".

Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.Cells
import Cb.Pv.Tail.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open TWhole

variable {K : Type} [Field K] {s : Size} (Λ : Letters K s)

/-- The cells: matrix, column, row. -/
abbrev JCell (s : Size) : Type := Σ μ : Fin s.NM, Fin (s.k μ) × Fin (s.m μ)

/-- The form of a read at a column: the read's weights on the cells of that column. -/
def affRead (x : Λ.X) : JTab s → Aff K (JCell s)
  | ⟨μ, r, c⟩ =>
    ⟨(formOf ((List.finRange (s.m μ)).map fun i => ((⟨μ, c, i⟩ : JCell s), Λ.w x μ r i)) 0).co, 0⟩

theorem agree_of_cells {x : Λ.X} {msg : Λ.M}
    {a : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (h : CellsOK Λ x msg a) :
    ∀ j : JTab s, Λ.tab msg j.1 j.2.1 j.2.2 =
      (affRead Λ x j).val fun j : JCell s => ((a j.1 j.2.1 j.2.2 : ℤ) : K) := by
  rintro ⟨μ, r, c⟩
  show Λ.tab msg μ r c = ∑ j, (formOf ((List.finRange (s.m μ)).map fun i =>
      ((⟨μ, c, i⟩ : JCell s), Λ.w x μ r i)) 0).co j *
        (fun j : JCell s => ((a j.1 j.2.1 j.2.2 : ℤ) : K)) j + 0
  rw [add_zero]
  unfold formOf
  rw [sum_formOf, List.map_map, sum_finRange]
  exact h.2.2 μ c r

theorem agree_of_relIn {x : Λ.X} {msg : Λ.M} (h : relIn Λ x msg) :
    ∃ a : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ,
      (∀ μ c i, |a μ c i| < 2 * (s.beta : ℤ)) ∧
      (∀ μ c i', Λ.sym msg μ i' c = ((Alg.pack (s.rad : ℤ) (a μ c) i' : ℤ) : K)) ∧
      ∀ j : JTab s, Λ.tab msg j.1 j.2.1 j.2.2 =
        (affRead Λ x j).val fun j : JCell s => ((a j.1 j.2.1 j.2.2 : ℤ) : K) := by
  obtain ⟨a, ha⟩ := cells_of_relIn Λ h
  exact ⟨a, ha.1, ha.2.1, agree_of_cells Λ ha⟩

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.agree_of_cells
#print axioms Cb.Pv.Tail.agree_of_relIn
