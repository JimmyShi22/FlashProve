-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/KeyOnceFacts.lean: small closed facts on the typed shape of the test on the table of
a key of full size (Params.keyOnceRec, OnBytes/Params/KeyOnceRecord.lean), each by evaluation.

Main names.
  keyOnce_sharedSplit   the folded row and Omega differ in code: the shared split is needed.
  keyOnce_ownSplit      W and Omega do not: a request's own split is not.
  keyOnce_form          masks ride and go ahead.

Limits. The typed value alone. Nothing on soundness.

-/
import OnBytes.Params.KeyOnceRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

theorem keyOnce_sharedSplit : keyOnceRec.shape.sharedSplitNeeded = true := by decide

theorem keyOnce_ownSplit : keyOnceRec.shape.ownSplitNeeded = false := by decide

theorem keyOnce_form : keyOnceRec.shape.choice.masksRide = true ∧
    keyOnceRec.shape.masksAhead = true := ⟨rfl, rfl⟩

end OnBytes.Params

#print axioms OnBytes.Params.keyOnce_sharedSplit
#print axioms OnBytes.Params.keyOnce_ownSplit
#print axioms OnBytes.Params.keyOnce_form
