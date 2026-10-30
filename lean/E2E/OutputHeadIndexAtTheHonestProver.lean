-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OutputHeadIndexAtTheHonestProver.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of the online
proof): THE TWO PREMISES THAT READ THE INDEX (IndexHeld, TraceIsTheModels:
Johnson/Desc/ProofFile/Honest/K6/Term/IndexPremises.lean) AT THE HONEST PROVER's INDEX, A MATRIX,
AND AT ITS READER AND TRACE (matrixInput, E2E/TheHonestProver.lean), FROM TWO PLAINER PREMISES.

WHAT IT IS NOT. The two plainer premises stay premises; where no input is valid all holds for
nothing. The trace of matrixInput is a definition by choice at the full size, which no program runs:
"the input's trace is the integer model's" follows here from that definition, not from a run.
Nothing says that the verifier accepts. One module under Johnson/Goal/ is imported by name
(Johnson/Goal/Meaning/NextToken.lean, for holds_of_indexOf). Nothing on soundness or on what a proof
hides.

WHAT IT IS.
  validInputCarriesTheTrace      the valid input's trace is what matrixInput.trace returns at the
                                 input's matrix and instance: a premise on the thread's letter Vd
  scriptCellsHoldTheInputsIndex  the cells that the Script makes of the valid input hold whatever
                                 index the input's matrix holds: a premise on the Script; it is met
                                 where these cells are the input's matrix

How. matrixInput.trace returns a trace only at a matrix that holds an index i, and then the
library's trace at i. A matrix of the full size's shape that holds i is the matrix of i's casts
(Flat.eq_matrixOf_of_holds), so its plain reader is the library's reader entryOf i
(Bind.ForProver.cellsReader_matrixOf).

  matrixReaderAtAHeldIndex, matrixTraceIsAtAHeldIndex   these two facts on matrixInput
  traceIsTheModelsAtTheMatrices, indexHeldAtTheMatrices the two premises
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K6.Term.IndexPremises
import Johnson.Bind.ForProver.MatrixReaders
import Johnson.Flat.MatrixOfImage
import Johnson.Goal.Meaning.NextToken

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds indexOf matrixOf)
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.K6.Term
open ProofFile.Honest.FirstThread (Script)
open P5J (AtMgA CellsM TS)

/-! ## 1 Two facts on the honest prover's reader and trace -/

/-- **At a matrix that holds an index the honest prover's reader of the committed digits is the
library's reader of that index.** -/
theorem matrixReaderAtAHeldIndex {M : FullSizeMatrix} {i : Cm.Idx} (holds : Holds M i) (publicPart : ProofFile.Pub) :
    matrixInput.weights publicPart M =
      (⟨OnBytes.HonestTrace.entryOf i⟩ : ProofFile.Honest.Weights) := by
  obtain rfl : M = matrixOf i := VerifiableInference.OnPublicFiles.Flat.eq_matrixOf_of_holds holds
  exact congrArg ProofFile.Honest.Weights.mk (Bind.ForProver.cellsReader_matrixOf i)

/-- **Where the honest prover has a trace, its matrix holds an index, and the trace is the library's
at that index.** -/
theorem matrixTraceIsAtAHeldIndex {M : FullSizeMatrix} {publicPart : ProofFile.Pub} {ξ : ProofFile.Inst}
    {trace : ProofFile.Honest.Cells} (traced : matrixInput.trace publicPart M ξ = some trace) :
    ∃ i : Cm.Idx, Holds M i ∧ ProofFile.Honest.fullIn.trace publicPart i ξ = some trace := by
  have e : (indexOf M).bind (fun i => ProofFile.Honest.fullIn.trace publicPart i ξ) = some trace := traced
  obtain ⟨i, found, atIndex⟩ := Option.bind_eq_some_iff.1 e
  exact ⟨i, VerifiableInference.Meaning.holds_of_indexOf found, atIndex⟩

/-! ## 2 The two premises that read the index -/

section Premises
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Rc : Type}
  {Vd : ProofFile.Honest.Local FullSizeMatrix Rc ProofFile.Inst ProofFile.Honest.Cells → Prop}
  {w : ProofFile.Honest.Local FullSizeMatrix Rc ProofFile.Inst ProofFile.Honest.Cells}

/-- CONDITIONAL on h, on "G is the blank ground" and on validInputCarriesTheTrace, which stays a
premise. **TraceIsTheModels at the honest prover's reader and trace.** It holds by the definition of
matrixInput.trace, which no program runs. -/
theorem traceIsTheModelsAtTheMatrices (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (groundIsBlank : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (validInputCarriesTheTrace : Vd w → matrixInput.trace Zp w.w₀ w.x = some w.trace) :
    TraceIsTheModels Zp G (matrixInput.weights Zp) Vd w :=
  traceIsTheModelsAtAnIndexReader h groundIsBlank fun valid =>
    let ⟨i, holds, atIndex⟩ := matrixTraceIsAtAHeldIndex (validInputCarriesTheTrace valid)
    ⟨i, matrixReaderAtAHeldIndex holds Zp, atIndex⟩

/-- CONDITIONAL on two premises, which stay. **IndexHeld at the honest prover's reader.** -/
theorem indexHeldAtTheMatrices {Bk : ProofFile.Honest.ProverCoinCounts}
    {Q : Script Bk (ProofFile.Honest.Local FullSizeMatrix Rc ProofFile.Inst ProofFile.Honest.Cells)
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (validInputCarriesTheTrace : Vd w → matrixInput.trace Zp w.w₀ w.x = some w.trace)
    (scriptCellsHoldTheInputsIndex : Vd w → ∀ i : Cm.Idx, Holds w.w₀ i → Holds (Q.cells w) i) :
    IndexHeld Q (matrixInput.weights Zp) Vd w :=
  indexHeldAtAnIndexReader fun valid =>
    let ⟨i, holds, _⟩ := matrixTraceIsAtAHeldIndex (validInputCarriesTheTrace valid)
    ⟨i, scriptCellsHoldTheInputsIndex valid i holds, matrixReaderAtAHeldIndex holds Zp⟩

end Premises

end AtPublicFiles.AtFiles.HonestTerm.OutputHead

#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.matrixReaderAtAHeldIndex
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.matrixTraceIsAtAHeldIndex
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.traceIsTheModelsAtTheMatrices
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.indexHeldAtTheMatrices
