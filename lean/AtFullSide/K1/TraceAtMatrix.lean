-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/TraceAtMatrix.lean: THE BINDER hI OF AtFullSide/K1/TieAtBase.lean, PAID AT THE TERM's VALUE matrixInput, by fullIn_trace_some.
OF COMPLETENESS's KIND: NOT IN FRONT OF A LAW OVER COINS. i and x are fixed only up to what cellOf reads.

NO PROPERTY IS CLAIMED.
-/
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open ProofFile.Honest.Term (matrixInput)
open OnBytes.HonestTrace (ServesAt theTrace)

/-- **At matrixInput the trace that the filling reads is the model's own.** -/
theorem trace_at_matrix (Zq : ProofFile.Pub) : ∀ u ξ C, matrixInput.trace Zq u ξ = some C → ∃ i x,
    C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X Zq) (theTrace (P5J.At.X Zq) i x) ∧
      ServesAt (P5J.At.X Zq) i x := by
  intro M ξ C h
  have h' : ((VerifiableInference.OnPublicFiles.Flat.indexOf M).bind fun i => fullIn.trace Zq i ξ) = some C := h
  cases hi : VerifiableInference.OnPublicFiles.Flat.indexOf M with
  | none =>
    rw [hi] at h'
    cases h'
  | some i =>
    rw [hi] at h'
    obtain ⟨x, -, hs, rfl⟩ := fullIn_trace_some h'
    exact ⟨i, x, rfl, hs⟩

/-- **The same, with the one index**: i is the index that the matrix holds. -/
theorem trace_at_matrix_index (Zq : ProofFile.Pub) : ∀ u ξ C, matrixInput.trace Zq u ξ = some C →
    ∃ i x, VerifiableInference.OnPublicFiles.Flat.indexOf u = some i ∧
      C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X Zq) (theTrace (P5J.At.X Zq) i x) ∧
      ServesAt (P5J.At.X Zq) i x := by
  intro M ξ C h
  have h' : ((VerifiableInference.OnPublicFiles.Flat.indexOf M).bind fun i => fullIn.trace Zq i ξ) = some C := h
  cases hi : VerifiableInference.OnPublicFiles.Flat.indexOf M with
  | none =>
    rw [hi] at h'
    cases h'
  | some i =>
    rw [hi] at h'
    obtain ⟨x, -, hs, rfl⟩ := fullIn_trace_some h'
    exact ⟨i, x, rfl, rfl, hs⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.trace_at_matrix
#print axioms ProofFile.Honest.K1.trace_at_matrix_index
