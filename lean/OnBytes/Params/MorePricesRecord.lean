-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/MorePricesRecord.lean: at the five groups of the proximity test in an entry's chain,
at the full-size lines of the setting "record with work", each typed radius is at least the upper
radius, as it is at most the lower one.

OnBytes/Params/GroupPricesRecord.lean shows that five typed radii are at most the lower radius of
their groups' distances. This file evaluates `upperRadiusTest` (OnBytes/Params/MorePrices.lean) in
Lean's kernel at the same groups and radii: each is at least the upper radius
(`record_groups_upper`). So at these groups one radius serves the laws on the closeness rounds and
the laws on the draws of positions.

Main theorem: `record_groups_upper`.
What is not claimed: what the heads of OnBytes/Params/MorePrices.lean and
OnBytes/Params/GroupPricesRecord.lean do not claim. That a typed radius equals the two radii: no law
here says that the lower radius is at most the upper one. For proofs only; the program, that is the
Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.MorePrices
import OnBytes.Params.GroupPricesRecord

set_option autoImplicit false

namespace OnBytes.Params

/-- At the five groups of the proximity test in an entry's chain, at the full-size lines of the
setting "record with work", the typed radii of OnBytes/Params/GroupPricesRecord.lean are also at
least the upper radius: each lies from the upper radius up to the lower one. -/
theorem record_groups_upper :
    upperRadiusTest recordSet recordG1 8342420 = true ∧
      upperRadiusTest recordSet recordG2 1569886 = true ∧
      upperRadiusTest recordSet recordG3 98104 = true ∧
      upperRadiusTest recordSet recordG4 6044 = true ∧
      upperRadiusTest recordSet recordG5 13370 = true := by decide +kernel

end OnBytes.Params

#print axioms OnBytes.Params.record_groups_upper
