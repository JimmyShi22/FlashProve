-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/HeadBase.lean: the lift of the output head's cells: behind the committed symbols
there are small integer matrices, and the head's cells are read in them.

Cb/Pv/Tail/Base.lean has BaseAt y Mz: the integers Mz are small, the committed symbols y are their
packing, and the cells that the one map cellValS reads off y are their images. There a cell has the
address (matrix, column, row), each below its bound. The verifier's rule cellsH
(Johnson/Road/HeadPlace.lean) reads the head's cells in matrices that are total functions of
(matrix, row, column).

matsOf s Mz: the total matrices: Mz with row and column swapped, and 0 outside the bounds. This is
the one place where the two orders meet. cellsAt s e: the same for values e of the cells in the
field. ic: the place of a cell among the entries J that claims read; a letter. tOfCells R s ic: the
dictionary: the head's cells, by the rule cellsH, from the entries at the cells' places.
HeadBase ic y e Mz: BaseAt y Mz, and the entries e have, at the cells' places, the cells that
cellValS reads off y. The packing clause in BaseAt is what HeadBase says: without it the statement
would hold of all symbols (weak_base, Cb/Pv/Tail/Base.lean). It is a member of a joint, with Mz a
part of the witness; as a hypothesis over all symbols it is false, for a prover may commit symbols
that are the packing of nothing small.
mzAt y: the integers behind the symbols y, as a function of y (cellsOf, Cb/Pv/Tail/Unique.lean): the
small integers with the packing y where there are such, and 0 elsewhere. baseAt_mzAt: BaseAt y
(mzAt y) holds exactly if there are integers Mz with BaseAt y Mz. So a joint may say HeadBase at
mzAt of the committed symbols: it names no further witness, it is false of symbols that are the
packing of nothing small, and the input relation of the smallness test's round gives it
(baseAt_of_relIn).
headBase_small, headBase_lift: under HeadBase the total matrices are below 2^18 in absolute value,
where twice the bound beta is at most 2^18; and the head's cells at the dictionary are what cellsH
reads in their casts.

What is not claimed. That the numbers of matrices, rows and columns of s are those of the head's
list, and that twice its beta is at most 2^18. That the swap is the right one is a matter of the two
rules that read the matrices: at total functions of three numbers a slip would type-check. This
file is not imported by the program.


-/
import Johnson.Road.Rows.HeadStart
import Cb.Pv.Tail.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Tail OnBytes.Road.Hd

/-- Matrices as total functions of (matrix, row, column): 0 outside the bounds. -/
def matsOf (s : Size) (Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) : Mats ℤ :=
  fun a r c =>
    if h : a < s.NM ∧ c < s.k a ∧ r < s.m a then Mz ⟨a, h.1⟩ ⟨c, h.2.1⟩ ⟨r, h.2.2⟩ else 0

/-- Values of the cells in the field, as total functions of (matrix, row, column). -/
def cellsAt (s : Size) (e : JCell s → Cb.Gl.E) : ℕ → ℕ → ℕ → Cb.Gl.E :=
  fun a r c =>
    if h : a < s.NM ∧ c < s.k a ∧ r < s.m a then e ⟨⟨a, h.1⟩, ⟨c, h.2.1⟩, ⟨r, h.2.2⟩⟩ else 0

/-- The dictionary: the head's cells from the entries at the cells' places. -/
def tOfCells (R : Model.Head.Run) (s : Size) {J : Type} (ic : JCell s → J) :
    (J → Cb.Gl.E) → Inst.Model.Head.Cells Cb.Gl.E :=
  fun e => cellsH R.h R.L R.b (cellsAt s fun j => e (ic j))

/-- Base: the committed symbols are the packing of small integers, and the entries' cells are the
cells behind the symbols. -/
def HeadBase {s : Size} {J : Type} (ic : JCell s → J) (y : Syms Cb.Gl.E s) (e : J → Cb.Gl.E)
    (Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) : Prop :=
  BaseAt y Mz ∧ ∀ j, e (ic j) = cellValS y j

/-- The integers behind the symbols y, as a function of y. -/
noncomputable def mzAt {s : Size} (y : Syms Cb.Gl.E s) :
    ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ :=
  Cb.Pv.Tail.cellsOf (symL Cb.Gl.E s) y

/-- At these integers BaseAt says that there are such integers. -/
theorem baseAt_mzAt {s : Size} (y : Syms Cb.Gl.E s) : BaseAt y (mzAt y) ↔ Base y :=
  ⟨fun h => ⟨_, h⟩, fun ⟨Mz, h⟩ =>
    ⟨fun μ c => (packs_cellsOf (symL Cb.Gl.E s) ⟨Mz μ c, h.1 μ c, h.2.1 μ c⟩).1,
      fun μ c => (packs_cellsOf (symL Cb.Gl.E s) ⟨Mz μ c, h.1 μ c, h.2.1 μ c⟩).2,
      fun _ => rfl⟩⟩

variable {s : Size} {J : Type} {ic : JCell s → J} {y : Syms Cb.Gl.E s} {e : J → Cb.Gl.E}
  {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ}

/-- The total matrices are small. -/
theorem headBase_small (hβ : 2 * (s.beta : ℤ) ≤ 2 ^ 18) (B : HeadBase ic y e Mz) (a r c : ℕ) :
    |matsOf s Mz a r c| < 2 ^ 18 := by
  unfold matsOf
  split
  · exact lt_of_lt_of_le (B.1.1 _ _ _) hβ
  · rw [abs_zero]
    norm_num

/-- The head's cells are what the verifier's rule reads in the casts of the total matrices. -/
theorem headBase_lift (R : Model.Head.Run) (B : HeadBase ic y e Mz) :
    tOfCells R s ic e =
      cellsH R.h R.L R.b fun a r c => ((matsOf s Mz a r c : ℤ) : Cb.Gl.E) := by
  refine congrArg (cellsH R.h R.L R.b) ?_
  funext a r c
  unfold cellsAt matsOf
  split
  · exact (B.2 _).trans (B.1.2.2 _)
  · exact Int.cast_zero.symm

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.baseAt_mzAt
#print axioms OnBytes.Road.Rows.headBase_small
#print axioms OnBytes.Road.Rows.headBase_lift
