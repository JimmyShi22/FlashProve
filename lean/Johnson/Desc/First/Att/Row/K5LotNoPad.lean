-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5LotNoPad.lean: kind K5's row: **THE Bool AT A PLAN (k5LotB,
Johnson/Desc/First/Att/Row/K5RowPlans.lean) FROM FOUR PARTS**: two that hang on the plan's field own
alone · "the padding keys are 0" · the rest of the claims' tests (claimsOkAtQ,
Johnson/Desc/First/Att/Row/K5DryNoPad.lean). A joining. NOTHING IS EVALUATED.
WHOSE EACH IS TO PAY: h₁ · h₂: numbers of own · h₃: by a law on the maker's text
(K5PadKeyOk.lean, beside this file) · h₄: WHAT IS LEFT FOR LEAN's KERNEL: A WALK AT THE PLAN.
Main name (namespace H2K5.Row): **k5LotB_of_Q**.
IS IT EMPTY HERE? AN IMPLICATION: none of the four is shown at any plan of any public file.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5RowPlans
import Johnson.Desc.First.Att.Row.K5DryNoPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P

/-- **THE Bool AT A PLAN, FROM FOUR PARTS.** -/
theorem k5LotB_of_Q {a : Attention.Plan} (h₁ : nRounds a.own = 162) (h₂ : planOkOwn a.own = true) (h₃ : padKeyOk (geoOf a.S) = true)
    (h₄ : claimsOkAtQ a = true) : k5LotB a = true := by
  unfold k5LotB
  rw [claimsOkAtT_Q, h₂, h₃, h₄, decide_eq_true h₁]
  rfl

end H2K5.Row

#print axioms H2K5.Row.k5LotB_of_Q
