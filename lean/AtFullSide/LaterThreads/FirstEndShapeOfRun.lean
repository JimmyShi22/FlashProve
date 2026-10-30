-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/FirstEndShapeOfRun.lean: CONDITIONAL ON TWO CLOSED FACTS: THE FIRST CHAIN's SHARE OF THE DOOR ON SHAPES (FirstEndHasTheShape,
AtFullSide/LaterThreads/DoorOnShapes.lean) WITH THE MARK ON THE PENDING ROW's WEIGHTS NOT A PREMISE: first_end_shape (FirstEndShape.lean) at
weights_at_reached (Johnson/AtFull/Shape/Scope/WeightsAtEnd.lean). One call.

  weights_at_the_end    WeightsAtTheEnd h, under the head alone
  first_end_shape_of_run  **FirstEndHasTheShape h a** from hW (the whole run on shapes at the stored files) and handedOf c = some a

Limits. hW (closed lines of the kernel, in a library of their own) and ha (one closed line at that run's end) ARE PREMISES: if the run
refused at one member the law would be empty. No thread, no prover, no coin. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.LaterThreads.FirstEndShape
import Johnson.AtFull.Shape.Scope.WeightsAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.LaterThreads
open ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn)
open Johnson.AtFull.Shape

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- The mark on the weights, under the head alone. -/
theorem weights_at_the_end (h : HeadAtReturn files A) : WeightsAtTheEnd h :=
  fun z s hr => Johnson.AtFull.Shape.Door.PileAt.weights_at_reached h.head z s hr

/-- **THE FIRST CHAIN's SHARE, FROM THE RUN AT THE STORED FILES.** -/
theorem first_end_shape_of_run (h : HeadAtReturn files A) {c : ShA} (hW : RunsAll 0 358 startShA c)
    {a : HandedShape} (ha : handedOf c = some a) : FirstEndHasTheShape h a :=
  first_end_shape h hW ha (weights_at_the_end h)

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.weights_at_the_end
#print axioms AtFullSide.LaterThreads.first_end_shape_of_run
