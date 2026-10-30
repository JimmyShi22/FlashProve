-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/DrawsAt1.lean: of the rounds of the key file's shared written plan at the
full size, 10 draw positions. A closed fact.

By `draws_of_lit` (DrawsByRuns.lean), then an evaluation in Lean's kernel (`decide +kernel`) along
the plan's runs.

Limits. That the written plan (`keyThree`, Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean) is the
planner's at any public files is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.DrawsByRuns
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open VerifiableInference.Number.ByRuns (keyThree)

set_option maxRecDepth 1000000 in
/-- The shared written plan has 10 rounds that draw positions. -/
theorem draws_at1 :
    (keyThree.B.plan.plan.rounds.filter fun e => Fmt.kindOf e.name == some .positions).length =
      10 := by
  rw [draws_of_lit]
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.draws_at1
