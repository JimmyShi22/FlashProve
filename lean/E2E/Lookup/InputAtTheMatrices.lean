-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/InputAtTheMatrices.lean: the lookups' premises on the input, at an index that is a matrix
of the full size's shape.

The honest online prover reads its index as such a matrix M: the weights by the plain reader of M's
cells, the trace through the index that M holds. This file shows that, wherever that trace is there,
the input meets InputHoldsTheHonestTrace (Honest/K3/Term/LookupDataAtTheHonestTrace.lean).

What is shown.
  matrixReaderIsTheIndexReader: the plain reader of such a matrix is the index's own reader.
  inputHoldsTheHonestTraceAtTheMatrices: the four premises, at some index and request.

Not claimed: that a prover's input has this trace; that is the frame's. Nothing on soundness,
completeness or zero knowledge.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupDataAtTheHonestTrace
import Johnson.Desc.ProofFile.Honest.AtPureFullIn
import Johnson.Bind.ForProver.MatrixReaders
import Johnson.Flat.MatrixOfImage
import Johnson.Goal.Meaning.NextToken
import E2E.ObjectAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Lookup
open VerifiableInference.OnPublicFiles (Flat.indexOf Flat.Holds Flat.eq_matrixOf_of_holds)
open OnBytes.HonestTrace (entryOf)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile (Pub Inst)
open ProofFile.Honest (Local Cells Weights fullIn fullIn_trace_some)
open ProofFile.Honest.K3.Term (InputHoldsTheHonestTrace)

/-- **The plain reader of a matrix that holds an index is the index's own reader.** -/
theorem matrixReaderIsTheIndexReader {M : FullSizeMatrix} {i : Cm.Idx} (h : Flat.indexOf M = some i) :
    AtPublicFiles.Key.cellsReader M = entryOf i := by
  have e : M = VerifiableInference.OnPublicFiles.Flat.matrixOf i :=
    Flat.eq_matrixOf_of_holds (VerifiableInference.Meaning.holds_of_indexOf h)
  rw [e]
  exact Bind.ForProver.cellsReader_matrixOf i

/-- **Wherever the trace through the matrix's index is there, the input holds the honest trace of a
served request.** -/
theorem inputHoldsTheHonestTraceAtTheMatrices {Rc : Type} (Zp : Pub) (t : Local FullSizeMatrix Rc Inst Cells)
    (h : ((Flat.indexOf t.w₀).bind fun i => fullIn.trace Zp i t.x) = some t.trace) :
    ∃ i x, InputHoldsTheHonestTrace Zp (fun M : FullSizeMatrix => (⟨AtPublicFiles.Key.cellsReader M⟩ : Weights)) t i x := by
  obtain ⟨i, hi, ht⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨x, hx, hs, e⟩ := fullIn_trace_some ht
  exact ⟨i, x, hs, e, by rw [matrixReaderIsTheIndexReader hi], hx⟩

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.matrixReaderIsTheIndexReader
#print axioms AtPublicFiles.Lookup.inputHoldsTheHonestTraceAtTheMatrices
