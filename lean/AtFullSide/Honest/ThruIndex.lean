-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/ThruIndex.lean: the value matrixInput of WiderIn (E2E/TheHonestProver.lean) reads
a matrix through Flat.indexOf. At a matrix that holds an index it answers what fullIn
(Honest/AtPureFullIn.lean) answers at that index; so laws on fullIn's trace and range speak of the
matrices that hold an index, and only of these.

  matrixInput_trace_of_holds, matrixInput_inRange_of_holds   at a matrix that holds i
  matrixInput_weights_of_holds, cellsReader_of_indexOf   the reader of the weights at a matrix that holds i:
                       matrixInput.weights reads the matrix, matrixInput.trace goes through indexOf: one index
  matrixInput_trace_at, matrixInput_inRange_at, matrixInput_weights_at   at matrixOf i
  matrixInput_trace_none     at a matrix that holds no index there is no trace

By what. Flat.indexOf_eq, Flat.holds_matrixOf (Johnson/Flat/LedgerClaim.lean);
Bind.ForProver.cellsReader_matrixOf (Johnson/Bind/ForProver/MatrixReaders.lean).

Limits.
  * Flat.indexOf is by choice: matrixInput is no program. Holds M i fixes i: the two maps agree by
    indexOf_eq alone.
  * Nothing on what the trace is beyond fullIn's laws.
  * Nothing on completeness, soundness or hiding.
-/
import E2E.TheHonestProver
import E2E.MatrixReaderAtIndex
import Johnson.Bind.ForProver.MatrixReaders
import Johnson.Flat.MatrixOfImage

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open VerifiableInference.OnPublicFiles.Flat (Holds indexOf indexOf_eq matrixOf holds_matrixOf InRange)
open OnBytes.HonestTrace (ServesAt theTrace)
open Inst.Model (Instance ppref)

/-- **At a matrix that holds i the trace is fullIn's at i.** -/
theorem matrixInput_trace_of_holds {M : FullSizeMatrix} {i : Cm.Idx} (h : Holds M i) (Zq : ProofFile.Pub) (ξ : ProofFile.Inst) :
    matrixInput.trace Zq M ξ = fullIn.trace Zq i ξ :=
  congrArg (fun o : Option Cm.Idx => o.bind fun i => fullIn.trace Zq i ξ)
    (indexOf_eq le_rfl le_rfl h)

/-- **Such a matrix is in range.** -/
theorem matrixInput_inRange_of_holds {M : FullSizeMatrix} {i : Cm.Idx} (h : Holds M i) : matrixInput.inRange M = true :=
  congrArg Option.isSome (indexOf_eq le_rfl le_rfl h)

/-- The trace at the matrix of an index. -/
theorem matrixInput_trace_at (i : Cm.Idx) (Zq : ProofFile.Pub) (ξ : ProofFile.Inst) :
    matrixInput.trace Zq (matrixOf i) ξ = fullIn.trace Zq i ξ :=
  matrixInput_trace_of_holds (holds_matrixOf i) Zq ξ

/-- The matrix of an index is in range. -/
theorem matrixInput_inRange_at (i : Cm.Idx) : matrixInput.inRange (matrixOf i) = true :=
  matrixInput_inRange_of_holds (holds_matrixOf i)

/-- The reader of the matrix of an index is the index's own. -/
theorem matrixInput_weights_at (Zq : ProofFile.Pub) (i : Cm.Idx) :
    matrixInput.weights Zq (matrixOf i) = fullIn.weights Zq i :=
  congrArg Weights.mk (Bind.ForProver.cellsReader_matrixOf i)

/-- **At a matrix that holds i the reader of the weights is the index's own.** -/
theorem matrixInput_weights_of_holds {M : FullSizeMatrix} {i : Cm.Idx} (h : Holds M i) (Zq : ProofFile.Pub) :
    matrixInput.weights Zq M = fullIn.weights Zq i := by
  have e : M = matrixOf i := VerifiableInference.OnPublicFiles.Flat.eq_matrixOf_of_holds h
  subst e
  exact matrixInput_weights_at Zq i

/-- **The reader of the matrix and the index that the trace goes through are one**: cellsReader M is
entryOf (indexOf M), wherever indexOf answers. -/
theorem cellsReader_of_indexOf {M : FullSizeMatrix} {i : Cm.Idx} (h : indexOf M = some i) :
    AtPublicFiles.Key.cellsReader M = OnBytes.HonestTrace.entryOf i := by
  have e : M = matrixOf i :=
    VerifiableInference.OnPublicFiles.Flat.eq_matrixOf_of_holds (holds_of_indexOf h)
  subst e
  exact Bind.ForProver.cellsReader_matrixOf i

/-- **A matrix that holds no index has no trace.** -/
theorem matrixInput_trace_none {M : FullSizeMatrix} (h : indexOf M = none) (Zq : ProofFile.Pub) (ξ : ProofFile.Inst) :
    matrixInput.trace Zq M ξ = none :=
  congrArg (fun o : Option Cm.Idx => o.bind fun i => fullIn.trace Zq i ξ) h

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.matrixInput_trace_of_holds
#print axioms ProofFile.Honest.Term.matrixInput_inRange_of_holds
#print axioms ProofFile.Honest.Term.matrixInput_trace_at
#print axioms ProofFile.Honest.Term.matrixInput_inRange_at
#print axioms ProofFile.Honest.Term.matrixInput_weights_at
#print axioms ProofFile.Honest.Term.matrixInput_weights_of_holds
#print axioms ProofFile.Honest.Term.cellsReader_of_indexOf
#print axioms ProofFile.Honest.Term.matrixInput_trace_none
