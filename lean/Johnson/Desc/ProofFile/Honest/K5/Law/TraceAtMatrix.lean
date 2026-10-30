-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/TraceAtMatrix.lean: conditional: at the prover that the maker
returns at the filling onlineProverPartsInUse matrixInput, an input that meets ReadyInput has a trace of
the full size at some index, as the premise TraceIsFull (TraceFull.lean in this folder) asks. No
definition.

  matrixTrace_through_full  each trace of matrixInput is a trace of fullIn at some index
  traceIsFull_at_base       TraceIsFull at the inputs that meet ReadyInput

How. matrixInput's trace is fullIn's at the index that the matrix holds, by its text. So the one
premise of traceIsFull_at_wider (TraceAtWider.lean in this folder) holds, and the maker's return and
the head are all that is left.

Limits. Conditional on the head at the return and on the maker's return. This is the base filling at
the coins IndexCommitterCoins, not the filling read through the object's randomness. The index and the instance
stand under "there is": nothing here ties them to the input's own fields. Where no trace returns no
input meets ReadyInput and the end says nothing. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K5.Law.TraceAtWider

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open VerifiableInference.OnPublicFiles.Flat (indexOf)

/-- **Each trace of matrixInput is a trace of fullIn at some index.** No premise. -/
theorem matrixTrace_through_full (Zp : ProofFile.Pub) (M : FullSizeMatrix) (ξ : ProofFile.Inst) (C : Cells)
    (e : matrixInput.trace Zp M ξ = some C) : ∃ i, fullIn.trace Zp i ξ = some C := by
  have e' : (indexOf M).bind (fun i => fullIn.trace Zp i ξ) = some C := e
  obtain ⟨i, -, hi⟩ := Option.bind_eq_some_iff.1 e'
  exact ⟨i, hi⟩

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **TraceIsFull at the base filling.** Conditional: the head at the return; the maker returns. -/
theorem traceIsFull_at_base (head : HeadAtReturn files A) (sizes : OnBytes.HonestTrace.Sz)
    (opening : OnlineProverArguments)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction sizes opening) = .ok A) :
    TraceIsFull (P5J.At.X A.Z) (ReadyInput head.description A.H) (id : Cells → Cells) :=
  traceIsFull_at_wider head matrixInput sizes opening made (matrixTrace_through_full A.Z)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.matrixTrace_through_full
#print axioms ProofFile.Honest.K5.traceIsFull_at_base
