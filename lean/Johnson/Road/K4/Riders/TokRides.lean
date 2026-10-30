-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/TokRides.lean: THE READER OF THE HEARD TOKEN, P5J.tokHOf
(Johnson/P5J/TokTerms.lean), GIVES ONE VALUE AT TWO STATES OF THE VERIFIER THAT PART INSIDE K4's
FENCE ALONE (LayRest, Johnson/Road/K4/K4Reads.lean). One statement.

  **`tokHOf_rides`**: LayRest s s' → tokHOf (z, s) = tokHOf (z, s'). No other premise.
Why: the reader reads the reply in the state's field out, which the fence keeps.
WHO SPENDS IT: the second half of the line head of the structure K4Fill
(Johnson/Road/K4/K4RowWideScope.lean), at tokH := tokHOf.
Limits. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4Reads
import Johnson.P5J.TokTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders
open VerifiableInference.Desc.First (S)

/-- **The heard token's reader rides inside K4's fence.** -/
theorem tokHOf_rides {P : Type} (z : P) {s s' : S} (h : LayRest s s') :
    P5J.tokHOf (z, s) = P5J.tokHOf (z, s') := by
  have e : s'.heardTok? = s.heardTok? := by
    unfold S.heardTok? S.heard
    rw [h.2.out]
  unfold P5J.tokHOf P5J.tokOfHeard
  show P5J.tokVOf (s.heardTok?.getD 0) = P5J.tokVOf (s'.heardTok?.getD 0)
  rw [e]

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.tokHOf_rides
