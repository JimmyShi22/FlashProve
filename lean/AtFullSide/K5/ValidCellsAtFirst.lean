-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K5/ValidCellsAtFirst.lean: conditional: a valid input's cells hold an index at the first
Script of the record at the base prover, at the filling's matrices. No definition.

  firstScript_cells_are_the_readers   the Script's cells are the matrix of cells of the index's reader
  validCellsHold_at_first             the premise of the kind K5 at that Script

Limits. Conditional on the maker's return. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import AtFullSide.K1.FirstScript
import Johnson.Desc.ProofFile.Honest.K5.Law.ValidCellsHold

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.K1 (firstScriptAt)
open VerifiableInference.OnPublicFiles (numsRef)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open OnBytes.Slice (frS frZ)
open Bind.ForProver (cellsOfF)
open VerifiableInference.Desc (Chain)
open P5J (TS)

variable {pol lay KL : ByteArray} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The first Script's cells are the matrix of cells of the index's reader.** No premise. -/
theorem firstScript_cells_are_the_readers (cF : Chain TS ProofFile.Cl)
    (v : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) :
    (firstScriptAt matrixInput S O A cF).cells v =
      cellsOfF frS frZ 402653181 numsRef (matrixInput.weights A.Z v.w₀).entry :=
  rfl

/-- **A VALID INPUT's CELLS HOLD, AT THE FIRST SCRIPT.** Conditional: the maker returns. -/
theorem validCellsHold_at_first {F : VerifiableInference.Desc.FileDescription ProofFile.Inst}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction pol lay KL (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S O) =
      .ok A)
    (cF : Chain TS ProofFile.Cl) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (valid : ReadyInput F A.H w) :
    ∃ i, Holds ((firstScriptAt matrixInput S O A cF).cells w) i :=
  validCellsHold_at_base made _ A.Z (firstScript_cells_are_the_readers cF) w valid

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.firstScript_cells_are_the_readers
#print axioms ProofFile.Honest.K5.validCellsHold_at_first
