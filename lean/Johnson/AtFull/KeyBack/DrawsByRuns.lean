-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/DrawsByRuns.lean: how many rounds of a written plan draw positions, counted
along its runs.

A written plan (`Lit`, Johnson/G/RunsDefs.lean) holds its distinct rounds once, and a list of runs:
how often, which. `fill` (Johnson/G/RoundsOfPlan.lean) counts the plan's rounds that draw positions.
Here that count is one walk along the runs (`cntG`, Johnson/G/Runs.lean), so its cost goes by the
number of runs and not by the number of rounds.

  `drawsRound e`: e is a round (its name is not "RECORD"), and it draws positions.
  `draws_of_lit`: the count, at a written plan. Its left side is `fill`'s own expression.

By calls: `entries_of_lit` (Johnson/Desc/Ok/NumberPrices/ByRuns.lean), `count_unrunG`
(Johnson/G/Runs.lean).

Limits. General in the written plan: no number is computed here. That a written plan is the
planner's at any public files is not said. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.Ok.NumberPrices.ByRuns
import Decl.Declared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open VerifiableInference.Number.ByRuns (Lit entries_of_lit)
open Johnson.G.Runs (valRuns cntG count_unrunG)

/-- An entry that is a round, and draws positions. -/
def drawsRound (e : Fmt.Entry) : Bool :=
  Fmt.kindOf e.name == some .positions && e.name != Fmt.recordName

/-- **The rounds of a written plan that draw positions, counted along the runs.** -/
theorem draws_of_lit (L : Lit) :
    (L.plan.plan.rounds.filter fun e => Fmt.kindOf e.name == some .positions).length =
      cntG drawsRound 0 (valRuns (L.recs.map (·.entry)) L.runs) := by
  unfold Fmt.Plan.rounds
  rw [List.filter_filter, entries_of_lit]
  exact count_unrunG drawsRound _ _

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.draws_of_lit
