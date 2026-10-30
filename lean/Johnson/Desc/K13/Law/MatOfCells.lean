-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/MatOfCells.lean: THE MATRIX THAT THE WITNESS's CELLS HOLD: the term that is
meant for the letter mat of the reader of the rows on the table (`rwBook arr mat`,
Johnson/Desc/K13/Law/ReaderByBook.lean). A definition and statements with their proofs.
  `cellAtNo c r j`: the cell at row r and column j by numbers: the cells' own entry inside both
  bounds; 0 outside.
  `matOfCells nR k c`: the matrix of nR rows and 2^k columns: row i, the column whose number has the
  bits b, the lowest first (`matBy`, Johnson/Desc/K13/Law/StepBack.lean; `Nat.ofBits`).
  `matOfCells_low`: at the column `lowBits k C` (Johnson/Desc/K13/Law/Eval.lean), C below 2^k, it is
  the cell at row i and column C.
  `matOfCells_in`: inside both bounds that is the cells' own entry.
  `matOfCells_zero`: from the cells' number of rows on it is 0; `matOfCells_zero_col`: so it is from
  their number of columns on.
What is not claimed. That any filling lays this term. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.StepBack
import Johnson.Desc.K13.Law.Eval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice

section
variable {rows cols : ℕ}

/-- The cell at a row and a column by numbers; 0 outside the bounds. -/
def cellAtNo (c : Fin rows → Fin cols → GE) (r j : ℕ) : GE :=
  if h : r < rows ∧ j < cols then c ⟨r, h.1⟩ ⟨j, h.2⟩ else 0

/-- **The matrix that the cells hold.** -/
def matOfCells (nR k : ℕ) (c : Fin rows → Fin cols → GE) : Fin nR → (Fin k → Bool) → GE :=
  matBy k (cellAtNo c)

/-- At the column with the number C. -/
theorem matOfCells_low (nR k : ℕ) (c : Fin rows → Fin cols → GE) (i : Fin nR) (C : ℕ)
    (hC : C < 2 ^ k) : matOfCells nR k c i (lowBits k C) = cellAtNo c i C := by
  unfold matOfCells matBy lowBits
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt hC]

/-- Inside both bounds: the cells' own entry. -/
theorem matOfCells_in (nR k : ℕ) (c : Fin rows → Fin cols → GE) (i : Fin nR) (C : ℕ)
    (hC : C < 2 ^ k) (hr : i.val < rows) (hc : C < cols) :
    matOfCells nR k c i (lowBits k C) = c ⟨i, hr⟩ ⟨C, hc⟩ := by
  rw [matOfCells_low nR k c i C hC]
  unfold cellAtNo
  rw [dif_pos ⟨hr, hc⟩]

/-- From the cells' number of rows on: 0. -/
theorem matOfCells_zero (nR k : ℕ) (c : Fin rows → Fin cols → GE) (i : Fin nR)
    (b : Fin k → Bool) (hr : rows ≤ i.val) : matOfCells nR k c i b = 0 := by
  unfold matOfCells matBy cellAtNo
  rw [dif_neg fun h => absurd h.1 (Nat.not_lt.2 hr)]

/-- From their number of columns on: 0. -/
theorem matOfCells_zero_col (nR k : ℕ) (c : Fin rows → Fin cols → GE) (i : Fin nR)
    (b : Fin k → Bool) (hc : cols ≤ Nat.ofBits b) : matOfCells nR k c i b = 0 := by
  unfold matOfCells matBy cellAtNo
  rw [dif_neg fun h => absurd h.2 (Nat.not_lt.2 hc)]

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.matOfCells_low
#print axioms VerifiableInference.Desc.K13.Law.matOfCells_in
#print axioms VerifiableInference.Desc.K13.Law.matOfCells_zero
#print axioms VerifiableInference.Desc.K13.Law.matOfCells_zero_col
