-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/EntersTokenAndCellsAtTheWrittenScript.lean

Nothing on hiding. No property of the protocol is claimed.
THE TOKEN AND THE CELLS OF THE SCRIPT. "firstScriptAt I S Op A cF" (AtFullSide/K1/FirstScript.lean) is the first chain's
Script at the BASE prover of the online proof, as a closed term. Its token is "tokB": the number of the field's element that
the instance asks about. Its cells are "cellsB I A.Z": the matrix of cells of the index's reader. Here: the two light clauses,
"cells" and "token", of "ScriptReadsTheInput" (Johnson/HonestTrace/Joint/EntersItemsOverMatrices.lean), at that Script.

Main theorems.
* "askedNumberIsTheFirstWord": at EVERY instance ξ, OnBytes.Desc.Reply.tokOf ξ.asked = ProofFile.Honest.K3.askedTok ξ. No premise: a
  32-bit word is below the prime (OnBytes.Flat.askedReplyOf_c0, Johnson/Flat/FinIsCanonical.lean). Not by rfl.
* "firstScriptTokenIsAsked": (firstScriptAt I S Op A cF).tok v = askedTok v.x, at every I, S, Op, A, cF, v and every type W₀ of
  the index. No premise.
* "firstScriptTokenMakesTheRequest": the clause "token" to the letter.
* "cellsOfTheReaderAreTheMatrix": at a matrix M that holds an index, the matrix of cells of M's own reader
  (AtPublicFiles.Key.cellsReader) is M.
* "firstScriptCellsAreTheMatrix", "firstScriptCellsHold": at W₀ := the matrices and an I whose reader at the input's matrix is
  that matrix's own reader: where the matrix holds an index, the Script's cells are the matrix; the clause "cells" to the letter.
* "…AtMatrixInput": the same at I := ProofFile.Honest.Term.matrixInput (E2E/TheHonestProver.lean), where the premise on I is paid by
  rfl.

Limits. THE BASE PROVER, NOT THE TERM's: the Script's inputs are Local W₀ IndexCommitterCoins ProofFile.Inst Cells; the online prover of
E2E/TheHonestProver.lean is the base prover read through OnlineProverParts.through, with another type of randomness: nothing here crosses
that. AT A MATRIX THAT HOLDS NO INDEX THE SCRIPT's CELLS NEED NOT BE THE MATRIX: the reader keeps a cell's first coordinate
alone. The clause "messages" is not touched. A is a letter: no return of the maker is shown.
-/
import Johnson.HonestTrace.Joint.EntersRequest
import AtFullSide.K1.FirstScript
import Johnson.Bind.ForProver.MatrixReaders
import Johnson.Flat.MatrixOfImage
import Johnson.Flat.FinIsCanonical
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Enters

open Inst.Model (ppref Instance)
open ProofFile.Honest (OnlineProverWithDescription IndexCommitterCoins Cells WiderIn OnlineProverArguments Weights)
open ProofFile.Honest.K1 (firstScriptAt LocB)
open ProofFile.Honest.K3 (askedTok)
open ProofFile.Honest.Term (matrixInput)
open VerifiableInference.Desc (Chain)
open VerifiableInference.OnPublicFiles (numsRef)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open OnBytes.Slice (frS frZ)
open Bind.ForProver (cellsOfF)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open P5J (TS)

/-! ## 1 The token -/

/-- **The number of the element that an instance asks about is the reply file's first word**, at every instance. -/
theorem askedNumberIsTheFirstWord (ξ : ProofFile.Inst) : OnBytes.Desc.Reply.tokOf ξ.asked = askedTok ξ :=
  OnBytes.Flat.askedReplyOf_c0 ξ.y

section Token
variable {W₀ : Type} (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
  (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (cF : Chain TS ProofFile.Cl) (v : LocB W₀)

/-- **THE REAL SCRIPT's TOKEN IS THE REPLY FILE's FIRST WORD.** No premise. -/
theorem firstScriptTokenIsAsked : (firstScriptAt I S Op A cF).tok v = askedTok v.x :=
  askedNumberIsTheFirstWord v.x

/-- **THE CLAUSE "token" OF ScriptReadsTheInput AT THE REAL SCRIPT, TO THE LETTER.** -/
theorem firstScriptTokenMakesTheRequest :
    ∀ x : Instance ppref, ProofFile.instOf v.x = some x →
      (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
        (P5J.tokVOf ((firstScriptAt I S Op A cF).tok v))).val = x :=
  fun _ read => scriptTiesRequestClause _ v read (firstScriptTokenIsAsked I S Op A cF v)

end Token

/-! ## 2 The cells -/

/-- **At a matrix that holds an index, the matrix of cells of the matrix's own reader is the matrix.** -/
theorem cellsOfTheReaderAreTheMatrix {M : FullSizeMatrix} {i : Cm.Idx} (held : Holds M i) :
    cellsOfF frS frZ 402653181 numsRef (AtPublicFiles.Key.cellsReader M) = M := by
  have e : M = VerifiableInference.OnPublicFiles.Flat.matrixOf i :=
    VerifiableInference.OnPublicFiles.Flat.eq_matrixOf_of_holds held
  subst e
  exact (congrArg (cellsOfF frS frZ 402653181 numsRef) (Bind.ForProver.cellsReader_matrixOf i)).trans
    (Bind.ForProver.cellsOfF_matrixOf i)

section CellsOfTheScript
variable (I : WiderIn FullSizeMatrix) (S : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
  (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (cF : Chain TS ProofFile.Cl) (v : LocB FullSizeMatrix)

/-- Where the input's matrix holds an index and I reads it by its own reader, the real Script's cells are that matrix. -/
theorem firstScriptCellsAreTheMatrix
    (readsTheMatrix : I.weights A.Z v.w₀ = ⟨AtPublicFiles.Key.cellsReader v.w₀⟩) {i : Cm.Idx}
    (held : Holds v.w₀ i) : (firstScriptAt I S Op A cF).cells v = v.w₀ := by
  show cellsOfF frS frZ 402653181 numsRef (I.weights A.Z v.w₀).entry = v.w₀
  rw [readsTheMatrix]
  exact cellsOfTheReaderAreTheMatrix held

/-- **THE CLAUSE "cells" OF ScriptReadsTheInput AT THE REAL SCRIPT, TO THE LETTER**, at an I that reads the input's matrix by
its own reader. -/
theorem firstScriptCellsHold (readsTheMatrix : I.weights A.Z v.w₀ = ⟨AtPublicFiles.Key.cellsReader v.w₀⟩) :
    ∀ i : Cm.Idx, Holds v.w₀ i → Holds ((firstScriptAt I S Op A cF).cells v) i := by
  intro i held
  rw [firstScriptCellsAreTheMatrix I S Op A cF v readsTheMatrix held]
  exact held

/-- At the term's own reader of the matrices. -/
theorem firstScriptCellsAreTheMatrixAtMatrixInput {i : Cm.Idx} (held : Holds v.w₀ i) :
    (firstScriptAt matrixInput S Op A cF).cells v = v.w₀ :=
  firstScriptCellsAreTheMatrix matrixInput S Op A cF v rfl held

/-- **The clause "cells" at the term's own reader of the matrices**: no premise is left. -/
theorem firstScriptCellsHoldAtMatrixInput :
    ∀ i : Cm.Idx, Holds v.w₀ i → Holds ((firstScriptAt matrixInput S Op A cF).cells v) i :=
  firstScriptCellsHold matrixInput S Op A cF v rfl

end CellsOfTheScript

end HonestTraceRun.Enters

#print axioms HonestTraceRun.Enters.askedNumberIsTheFirstWord
#print axioms HonestTraceRun.Enters.firstScriptTokenIsAsked
#print axioms HonestTraceRun.Enters.firstScriptTokenMakesTheRequest
#print axioms HonestTraceRun.Enters.cellsOfTheReaderAreTheMatrix
#print axioms HonestTraceRun.Enters.firstScriptCellsAreTheMatrix
#print axioms HonestTraceRun.Enters.firstScriptCellsHold
#print axioms HonestTraceRun.Enters.firstScriptCellsAreTheMatrixAtMatrixInput
#print axioms HonestTraceRun.Enters.firstScriptCellsHoldAtMatrixInput
