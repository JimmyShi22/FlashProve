-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/TraceAtWider.lean: conditional: at a return of the maker at the
filling onlineProverPartsInUse, the premise on the trace (TraceIsFull, TraceFull.lean in this folder)
follows from one premise on the index's reader I: each of its traces is a trace of fullIn at some
index. No definition; one theorem.

  traceIsFull_at_wider   TraceIsFull at the inputs that meet ReadyInput

The premises, all of them: h, the head at the return; made, the maker returns A at the filling;
throughFull, the premise on I, at the return's public part. I is a letter here.

How. ReadyInput's third clause says that the prover's trace returns; atPure_ok's fourth that it is
the filling's, and that is I.trace; throughFull gives an index; fullIn_trace_some (AtPureFullIn.lean)
gives the serving and the trace; traceIsFull_of_cellOf (TraceFull.lean) closes it. The index that
TraceIsFull names is the one that throughFull gives, not the input's own field w₀.

Limits. Conditional. At a reader none of whose traces returns, throughFull says nothing, and nor does
the end. This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.TraceFull
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.AtPureFullIn
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open ProofFile.Honest.FirstThread (HeadAtReturn)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **At a return of the maker, the premise on the trace follows from one premise on the reader.**
Conditional: every premise stands, by name, in the file's head. -/
theorem traceIsFull_at_wider (h : HeadAtReturn files A) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (throughFull : ∀ w ξ C, I.trace A.Z w ξ = some C → ∃ i, fullIn.trace A.Z i ξ = some C) :
    TraceIsFull (P5J.At.X A.Z) (ReadyInput h.description A.H) (id : Cells → Cells) := by
  refine traceIsFull_of_cellOf h.head (fun v hv => ?_)
  obtain ⟨-, -, -, hT, -⟩ := atPure_ok made
  have ht : A.H.trace v.w₀ v.x = some v.trace := hv.2.2
  rw [hT] at ht
  obtain ⟨i, hi⟩ := throughFull v.w₀ v.x v.trace ht
  obtain ⟨x', -, hs, e⟩ := fullIn_trace_some hi
  refine ⟨OnBytes.HonestTrace.plOf (P5J.At.X A.Z) i x', i, x', hs, fun l s r c => ?_⟩
  exact congrArg (fun C : Cells => C.cell l s r c) e

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.traceIsFull_at_wider
