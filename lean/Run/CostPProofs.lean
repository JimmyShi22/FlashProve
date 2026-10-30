-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CostPProofs.lean: the proof of the statement of Run/CostP.lean.

Main names (statements and hypotheses: Run/CostP.lean):
  `costP_cost`: c.cost.le x t ↔ c.le x t at the condition that always holds.
It holds by definition. What a count says depends on the instance c: Run/CostP.lean, the head, 4.
-/
import Run.CostP

set_option autoImplicit false

namespace Run

theorem costP_cost : Spec.costP_cost := fun _ _ _ _ _ _ => Iff.rfl

end Run
