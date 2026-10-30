-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/CellsOfIndex.lean: the proof of the statement of
Johnson/Desc/ProofFile/Honest/K11/Plays/CellsOfIndexStatement.lean, to the letter. A lemma; none of
the library's goals.

How. inRange: `InRange` is "there is an index that the matrix holds"
(Johnson/Flat/LedgerClaim.lean). entries: the reading of the reader's entry is its image in the
extension field (`readE_ofF`, OnBytes/Slice/ProgField.lean; `toF_ofF`, OnBytes/Slice/Field.lean),
which the premise's second clause gives as the image of the index's matrix's entry; inside the
cells' shape the cell is that image, outside it the cell is read as 0 (`cellAtNo`,
Johnson/Desc/K13/Law/MatOfCells.lean) and the index's matrix is 0 (the two clauses of `SaysC`,
LedgerClaim.lean). The two bounds of the field entries are not spent.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.CellsOfIndexStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (Reading)
open VerifiableInference.Desc.K13.Law (cellAtNo)

/-- **The kind's premise on the cells, from one clause under Vd.** -/
theorem cellsOfIndex : CellsOfIndex := by
  intro Bk W₀ Rc Tr Q lay weights Vd h
  refine ⟨fun v hv => ?_, fun v hv r c _ _ => ?_⟩
  · obtain ⟨i, hi, -⟩ := h v hv
    exact ⟨i, hi⟩
  · obtain ⟨i, ⟨h1, h2⟩, h3⟩ := h v hv
    have e : Reading.gl.val (eOfF ((weights v.w₀).entry r c)) = ((i.mat r c : ℤ) : Cb.Gl.E) := by
      rw [← h3 r c]
      show OnBytes.Slice.readE (OnBytes.ofF (OnBytes.Slice.ofF _)) = _
      rw [OnBytes.Slice.readE_ofF, OnBytes.Slice.toF_ofF]
    rw [e]
    unfold cellAtNo
    by_cases hh : r < OnBytes.Flat.numsFull.rows ∧ c < P5J.colsAt OnBytes.Flat.numsFull
    · rw [dif_pos hh]
      exact h1 ⟨r, hh.1⟩ ⟨c, hh.2⟩
    · rw [dif_neg hh, h2 r c hh]
      exact Int.cast_zero.symm

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.cellsOfIndex
