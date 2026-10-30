-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ValidCellsHold.lean: conditional: at the prover that the maker
returns at the filling onlineProverPartsInUse matrixInput, the cells of an input that passes the range
test hold an index, where the Script's cells are the matrix of cells of the index's reader. No
definition.

  matrixInput_inRange_iff    a matrix passes matrixInput's range test exactly when it holds an index
  matrixInput_dummy_inRange  the named member of the range passes the test
  readers_matrix_of_holds    a matrix that holds an index is the matrix of cells of its own reader
  inRange_at_base            the returned prover's range test is matrixInput's
  admittedCellsHold_at_base  under "the index is in range and the trace the prover's", the Script's
                             cells hold an index, and the Script's cells are the input's matrix
  validCellsHold_at_base     the same at an input that meets ReadyInput

Why. The laws on the kind K5 take as a premise that the Script's cells at a valid input hold some
index. That premise does not say which model ran: it only keeps the items that the row asks in front
of the member from being idle. So it is paid by the range clause of the valid input alone, and the
trace clause is not spent.

The reader of matrixInput keeps a cell's first coordinate alone, so the matrix of cells of that
reader differs from the matrix at a cell outside the base field. A matrix that holds an index has no
such cell: each of its cells is the cast of an integer. So at an input in range the two are one.

The one premise beyond the maker's return is cellsAreTheReaders: the Script's cells are the matrix of
cells of the index's reader. The Script is a free field of the first thread's parts, so a law that
speaks of every Script needs such a clause. At a Script laid with that matrix as its cells the clause
holds by definition.

Limits. Conditional on the maker's return and on cellsAreTheReaders. The index stands under "there
is": nothing here says that it is the index at which the trace was computed, that the trace is a
correct run of a model, or that any input meets ReadyInput. Paying this premise does not pay the
identities on the segment: they come from the items that the thread's invariant holds in front of
the member, and whoever shows that a run meets that invariant owes them. This file proves nothing
about soundness, completeness, hiding or any other property of the protocol.
-/
import E2E.TheHonestProver
import Johnson.Bind.ForProver.CellsInField
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (Script)
open VerifiableInference.OnPublicFiles (numsRef numsRef_fits)
open VerifiableInference.OnPublicFiles.Flat (Holds indexOf indexOf_eq)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Slice (frS frZ GF GE)
open Bind.ForProver (cellsOfF)
open P5J (CellsM)

/-- **A matrix passes matrixInput's range test exactly when it holds an index.** No premise. -/
theorem matrixInput_inRange_iff (M : FullSizeMatrix) : matrixInput.inRange M = true ↔ ∃ i, Holds M i := by
  constructor
  · intro h
    have hs : (indexOf M).isSome = true := h
    by_contra hn
    have e : indexOf M = none := by
      unfold indexOf
      exact dif_neg hn
    rw [e] at hs
    cases hs
  · rintro ⟨i, hi⟩
    show (indexOf M).isSome = true
    rw [indexOf_eq numsRef_fits.1 numsRef_fits.2 hi]
    rfl

/-- **The named member of the range passes the test.** So the range is not empty. No premise. -/
theorem matrixInput_dummy_inRange : matrixInput.inRange matrixInput.dummy = true :=
  (matrixInput_inRange_iff _).2 ⟨fullIn.dummy, VerifiableInference.OnPublicFiles.Flat.holds_matrixOf _⟩

/-- **A matrix that holds an index is the matrix of cells of its own reader.** Conditional: it holds
an index; the reader drops a cell's other coordinates, and here they are 0. -/
theorem readers_matrix_of_holds (M : FullSizeMatrix) {i : Cm.Idx} (hold : Holds M i) :
    cellsOfF frS frZ 402653181 numsRef (AtPublicFiles.Key.cellsReader M) = M := by
  funext y c
  show algebraMap GF GE (AtPublicFiles.Key.cellsReader M y.val c.val) = M y c
  have e : AtPublicFiles.Key.cellsReader M y.val c.val = (M y c).c0 := by
    unfold AtPublicFiles.Key.cellsReader
    exact Eq.trans (dif_pos ⟨y.isLt, c.isLt⟩) rfl
  have hc : M y c = algebraMap GF GE ((i.mat y.val c.val : ℤ) : GF) := by
    rw [hold.1 y c, map_intCast]
  rw [e, hc]
  rfl

section
variable {pol lay KL : ByteArray} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The returned prover's range test is matrixInput's.** Conditional: the maker returns. -/
theorem inRange_at_base
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction pol lay KL (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S O) =
      .ok A) : A.H.inRange = matrixInput.inRange :=
  (atPure_ok made).2.2.2.2.2.1

variable {Bk : ProverCoinCounts}

/-- **At an input whose index is in range the Script's cells are the input's matrix, and hold an
index.** Conditional: the maker returns; cellsAreTheReaders. The trace clause is not spent. -/
theorem admittedCellsHold_at_base
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction pol lay KL (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S O) =
      .ok A)
    (Q : Script Bk (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (Zq : ProofFile.Pub)
    (cellsAreTheReaders : ∀ v, Q.cells v =
      cellsOfF frS frZ 402653181 numsRef (matrixInput.weights Zq v.w₀).entry)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (admitted : A.H.inRange w.w₀ = true ∧ A.H.trace w.w₀ w.x = some w.trace) :
    Q.cells w = w.w₀ ∧ ∃ i, Holds (Q.cells w) i := by
  have hr : matrixInput.inRange w.w₀ = true := by
    rw [← inRange_at_base made]
    exact admitted.1
  obtain ⟨i, hi⟩ := (matrixInput_inRange_iff _).1 hr
  have e : Q.cells w = w.w₀ :=
    (cellsAreTheReaders w).trans (readers_matrix_of_holds w.w₀ hi)
  refine ⟨e, i, ?_⟩
  rw [e]
  exact hi

/-- **A VALID INPUT's CELLS HOLD.** At every description F, an input that meets ReadyInput at the
returned prover has an index that the Script's cells hold. Conditional: the maker returns;
cellsAreTheReaders. -/
theorem validCellsHold_at_base {F : VerifiableInference.Desc.FileDescription ProofFile.Inst}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction pol lay KL (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S O) =
      .ok A)
    (Q : Script Bk (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (Zq : ProofFile.Pub)
    (cellsAreTheReaders : ∀ v, Q.cells v =
      cellsOfF frS frZ 402653181 numsRef (matrixInput.weights Zq v.w₀).entry)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (valid : ReadyInput F A.H w) :
    ∃ i, Holds (Q.cells w) i :=
  (admittedCellsHold_at_base made Q Zq cellsAreTheReaders w valid.2).2

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.matrixInput_inRange_iff
#print axioms ProofFile.Honest.K5.matrixInput_dummy_inRange
#print axioms ProofFile.Honest.K5.readers_matrix_of_holds
#print axioms ProofFile.Honest.K5.inRange_at_base
#print axioms ProofFile.Honest.K5.admittedCellsHold_at_base
#print axioms ProofFile.Honest.K5.validCellsHold_at_base
