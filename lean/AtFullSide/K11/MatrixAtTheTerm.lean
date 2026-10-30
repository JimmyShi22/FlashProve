-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/MatrixAtTheTerm.lean: the premise on the cells of K11ScriptAtTheTerm at matrixInput:
the index of the online prover is a matrix, the script's cells are that matrix, and a matrix in range
holds an index whose entries its reader reads.

  holds_of_inRange     a matrix in the filling's range holds an index
  reader_is_mat        the matrix's reader is that index's entries, in the extension field
  cells_at_matrixInput the premise, at the cells id
-/
import E2E.TheHonestProver
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open VerifiableInference.OnPublicFiles.Flat (Holds)
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- A matrix in the filling's range holds an index. -/
theorem holds_of_inRange {M : FullSizeMatrix} (h : matrixInput.inRange M = true) : ∃ i : Cm.Idx, Holds M i := by
  have h' : (VerifiableInference.OnPublicFiles.Flat.indexOf M).isSome = true := h
  unfold VerifiableInference.OnPublicFiles.Flat.indexOf at h'
  split at h'
  · rename_i hin
    exact hin
  · cases h'

/-- The matrix's reader is the index's entries, in the extension field. -/
theorem reader_is_mat {M : FullSizeMatrix} {i : Cm.Idx} (hH : Holds M i) (a b : Nat) :
    algebraMap Cb.Gl.F Cb.Gl.E (AtPublicFiles.Key.cellsReader M a b) = ((i.mat a b : ℤ) : Cb.Gl.E) := by
  unfold AtPublicFiles.Key.cellsReader
  split
  · rename_i hab
    have hc := hH.1 ⟨a, hab.1⟩ ⟨b, hab.2⟩
    have e : ((i.mat a b : ℤ) : Cb.Gl.E) =
        algebraMap Cb.Gl.F Cb.Gl.E ((i.mat a b : ℤ) : Cb.Gl.F) :=
      (map_intCast (algebraMap Cb.Gl.F Cb.Gl.E) (i.mat a b)).symm
    rw [hc, e]
    rfl
  · rename_i hab
    rw [hH.2 a b hab]
    simp

/-- **The premise on the cells, at the online prover's index.** -/
theorem cells_at_matrixInput (Zp : ProofFile.Pub) (M : FullSizeMatrix) (h : matrixInput.inRange M = true) :
    ∃ i : Cm.Idx, Holds M i ∧ ∀ a b, algebraMap Cb.Gl.F Cb.Gl.E ((matrixInput.weights Zp M).entry a b) =
      ((i.mat a b : ℤ) : Cb.Gl.E) := by
  obtain ⟨i, hi⟩ := holds_of_inRange h
  exact ⟨i, hi, reader_is_mat hi⟩

end AtFullSide.K11

#print axioms AtFullSide.K11.holds_of_inRange
#print axioms AtFullSide.K11.reader_is_mat
#print axioms AtFullSide.K11.cells_at_matrixInput
