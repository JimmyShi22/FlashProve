-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/SignsLetters.lean: four abbreviations and four small statements with their proofs.

What is here. The letters at which the column hX of the frame's gathering at the members of the
feed-forward layers' own rounds (sub-protocol K4) is laid AT THE BASE PROVER's VALUES: the
base filling, the first chain's Script `firstScriptAt` (AtFullSide/K1/FirstScript.lean), the valid
inputs
`ReadyInput`, the senders' readers. And what `k4_exchange_all_items`
(Honest/K4/Law/W/ExchangeAllItems.lean) asks of the index and its reader there:
  `trace_at_index`   what the base filling's trace returns, `fullIn`'s returns at the matrix's index
  `reader_at_index`   the reader of a matrix that holds an index is the index's reader
  `script_cells`   the Script's cells are the matrix of the index
  `readers_cells`   the readers' cells are the input's trace

Not shown here. AT THE BASE MAKER's RETURN, AT `IndexCommitterCoins`: NOT AT THE ONLINE MAKER's RETURN
(`onlineFilling`, E2E/TheHonestProver.lean, is this filling read through `OnlineProverParts.through`): the
crossing is another house's. That any input is valid. THE FULL SIZE ALONE, and the format's second
hash function alone.
`script_cells` FIXES WHAT THE SCRIPT's CELLS ARE AS A FUNCTION OF THE HIDDEN INDEX: of
completeness's kind: NOT IN FRONT OF A LAW OVER COINS. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import E2E.MatrixReaderAtIndex
import AtFullSide.K1.FirstScript
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Bind.ForProver.JoinsSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K4.Signs
open ProofFile ProofFile.Honest
open ProofFile.Honest.Term (matrixInput holds_of_indexOf cellsReader_of_holds matrixReaderIsIndexReader)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.K1 (firstScriptAt LocB)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes OnBytes.Model
open OnBytes.HonestTrace (Sz entryOf)
open VerifiableInference.OnPublicFiles.Flat (matrixOf indexOf)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- The base filling. -/
noncomputable abbrev baseFilling : OnlineProverParts FullSizeMatrix IndexCommitterCoins Cells Unit Unit :=
  onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest

/-- The first chain's Script at the base prover of the online proof. -/
noncomputable abbrev theScript (h : HeadAtReturn files A) :=
  firstScriptAt matrixInput Sz.ref openHonest A h.firstChain

/-- The valid inputs of the first thread. -/
abbrev validInput (h : HeadAtReturn files A) : LocB FullSizeMatrix → Prop := ReadyInput h.description A.H

/-- How the filling's senders read an input. -/
noncomputable abbrev readersAt (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) : LocB FullSizeMatrix → Readers :=
  fun v => ⟨v.trace, matrixInput.weights A.Z v.w₀, v.rc⟩

/-! ## Proved -/

/-- (5a) **What the base filling's trace returns, `fullIn`'s trace returns at the matrix's index.**
-/
theorem trace_at_index (Zq : ProofFile.Pub) (M : FullSizeMatrix) (ξ : ProofFile.Inst) (tr : Cells)
    (ht : baseFilling.trace Zq M ξ = some tr) :
    ∃ i, indexOf M = some i ∧ fullIn.trace Zq i ξ = some tr :=
  Option.bind_eq_some_iff.1 ht

/-- (5b) **The reader of a matrix that holds an index is the index's reader.** -/
theorem reader_at_index (Zq : ProofFile.Pub) (M : FullSizeMatrix) (i : Cm.Idx) (hi : indexOf M = some i) :
    matrixInput.weights Zq M = ⟨entryOf i⟩ :=
  matrixReaderIsIndexReader Zq M i hi

/-- (4) **The Script's cells are the matrix of the index.** Nothing is asked of the input but that
its matrix holds the index. -/
theorem script_cells (h : HeadAtReturn files A) (v : LocB FullSizeMatrix) (i : Cm.Idx)
    (hi : indexOf v.w₀ = some i) : (theScript h).cells v = matrixOf i := by
  have e : (matrixInput.weights A.Z v.w₀).entry = fun y c => ((i.mat y c : ℤ) : Cb.Gl.F) := by
    rw [reader_at_index A.Z v.w₀ i hi]
    rfl
  show Bind.ForProver.cellsOfF OnBytes.Slice.frS OnBytes.Slice.frZ 402653181
    VerifiableInference.OnPublicFiles.numsRef (matrixInput.weights A.Z v.w₀).entry = matrixOf i
  rw [e]
  exact Bind.ForProver.cellsOfF_matrixOf i

/-- The readers' cells are the input's trace. -/
theorem readers_cells (v : LocB FullSizeMatrix) : (readersAt A v).cells = v.trace := rfl

end AtFullSide.K4.Signs

#print axioms AtFullSide.K4.Signs.trace_at_index
#print axioms AtFullSide.K4.Signs.reader_at_index
#print axioms AtFullSide.K4.Signs.script_cells
#print axioms AtFullSide.K4.Signs.readers_cells
