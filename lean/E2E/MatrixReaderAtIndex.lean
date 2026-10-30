-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/MatrixReaderAtIndex.lean: the online prover's two readings of its matrix.

1. The online prover's input is a matrix M of cells (matrixInput, E2E/TheHonestProver.lean).
2. It reads M in two ways. Its reader of the index's digits reads M itself, cell by cell
   (AtPublicFiles.Key.cellsReader: the first coordinate of a cell, 0 outside the shape).
3. The trace is reached through the index that M holds (Flat.indexOf), and fullIn reads the digits
   of an index by OnBytes.HonestTrace.entryOf.
4. The proposition MatrixReaderIsIndexReader says that these are one reader: where M holds the
   index i, matrixInput's reader at M is fullIn's reader at i, at every public part.
5. A matrix holds an index when each cell is the cast of that index's digit at the same row and
   column, and the digits outside the matrix's shape are 0 (Flat.Holds).
6. holds_of_indexOf: what indexOf returns is held by the matrix.
7. cellsReader_of_holds: at a matrix that holds an index, the two functions agree at every row and
   column, inside the shape and outside it.
8. The file imports the definition of the online prover and changes nothing in it.
9. No hash, coin or oracle enters.
10. Neither reader reads the public part.
-/
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles (FullSizeMatrix)
open VerifiableInference.OnPublicFiles

/-- **What indexOf returns is held by the matrix.** -/
theorem holds_of_indexOf {rows cols : ℕ} {M : Fin rows → Fin cols → Flat.GE} {i : Cm.Idx}
    (h : Flat.indexOf M = some i) : Flat.Holds M i := by
  unfold Flat.indexOf at h
  split at h
  · rename_i hin
    have e : hin.choose = i := Option.some.inj h
    exact e ▸ hin.choose_spec
  · exact absurd h (by simp)

/-- **At a matrix that holds an index, the cell reader is the index's reader.** -/
theorem cellsReader_of_holds {rows cols : ℕ} {M : Fin rows → Fin cols → Flat.GE} {i : Cm.Idx}
    (h : Flat.Holds M i) (y c : ℕ) :
    AtPublicFiles.Key.cellsReader M y c = OnBytes.HonestTrace.entryOf i y c := by
  unfold AtPublicFiles.Key.cellsReader
  split
  · rename_i hin
    rw [h.1 ⟨y, hin.1⟩ ⟨c, hin.2⟩]
    rfl
  · rename_i hn
    show (0 : Cb.Gl.F) = ((i.mat y c : ℤ) : Cb.Gl.F)
    rw [h.2 y c hn, Int.cast_zero]

/-- **The two readings of the matrix are one**: where the matrix holds an index, the reader of the
online prover's input at the matrix is the reader of that index, at every public part. -/
def MatrixReaderIsIndexReader : Prop :=
  ∀ (publicPart : ProofFile.Pub) (M : FullSizeMatrix) (i : Cm.Idx), Flat.indexOf M = some i →
    matrixInput.weights publicPart M = fullIn.weights publicPart i

theorem matrixReaderIsIndexReader : MatrixReaderIsIndexReader := by
  intro publicPart M i h
  show (⟨AtPublicFiles.Key.cellsReader M⟩ : ProofFile.Honest.Weights) = ⟨OnBytes.HonestTrace.entryOf i⟩
  congr 1
  funext y c
  exact cellsReader_of_holds (holds_of_indexOf h) y c

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.holds_of_indexOf
#print axioms ProofFile.Honest.Term.cellsReader_of_holds
#print axioms ProofFile.Honest.Term.matrixReaderIsIndexReader
