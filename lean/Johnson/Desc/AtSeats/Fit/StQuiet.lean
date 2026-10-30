-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/StQuiet.lean: WHAT A RELATION ON THE STATEMENT OWES, THE
ADMITTING OF A SAMPLE APART: StQuiet R: quiet : GroundQuiet R · begun (the beginning of a proximity
test, AT A GROUP THAT IS THERE) · row (the one write of a pending row). It is StKeeps
(Johnson/Desc/K13/Law/StatementCalls.lean) with GroundQuiet in GroundKeeps' place and one premise
more at begun.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.StatementCalls
import Johnson.Desc.GroundQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.Ground (GroundQuiet)

/-- **What a relation on the statement owes**, the admitting of a sample apart. -/
structure StQuiet (R : Statement → Statement → Prop) : Prop where
  quiet : GroundQuiet R
  begun : ∀ (T : Statement) (g : Nat) (G : Group), T.groups[g]? = some G → R T (begun T g G)
  row : ∀ (lay : WsLay) (im : ℕ) (o : WsForkOut) (n : ℕ) (lin : LinShape) (T : Statement)
    (r : TensorRow) (os' : Array OnBytes.Oracle),
    pendingRowO lay im o n lin T.oracles = .ok (r, os') → R T { T with oracles := os' }

end VerifiableInference.Desc.K13.Law
