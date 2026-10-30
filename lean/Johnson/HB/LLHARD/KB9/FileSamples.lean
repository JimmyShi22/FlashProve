-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/FileSamples.lean: THE SMALL PREMISE OF `sends_of_from` AND `made_of_from`
(Johnson/HB/LLHARD/KB9/FileSends.lean) ON THE NUMBER OF ANSWERS, SHOWN AT THE WRITTEN VALUES: the
one-time chain's plan as read has as many answers to an out-of-domain sample as the planner's
setting.

  `samples_written`: a closed fact, by Lean's kernel (`decide +kernel`): the key file's first
    written priced plan (`keyThree.A`, Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean), as it is
    written into parameter bytes, has `recordSet`'s number of answers. A planner's plan takes that
    word from its own setting, by definition (`Planned.plan`, OnBytes/Params/Planner.lean).
    `samples_rejects`: the negative test: not one more. THE SAME FACT STANDS UNDER A SECOND NAME:
    `Johnson.KB4.samples_W` (Johnson/HB/LLHARD/KB4/Pins.lean), kept on purpose: that file is to lean
    on no file of this folder.
  **`ha_of`**: where the plan as read is that written plan and the sized setting is `recordSet`: the
    premise ha, to the letter.

Limits. The full size alone. The two equations are premises: `IM.keyPlans_at_made`
(Johnson/IMR/KeyPlansAtMade.lean) gives both at what `Key.madeAt` returns, for public files in scope
of the goals; that `publicOfO` and `Key.madeAt` return are premises there. Nothing on soundness.

-/
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten
import OnBytes.Params.Chains
import OnBytes.Params.Configure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params
open VerifiableInference.Number.ByRuns (keyThree)

/-- The first written plan's number of answers is the written setting's. -/
theorem samples_written : keyThree.A.plan.plan.samples = recordSet.samples := by decide +kernel

/-- The negative test: not one more. -/
theorem samples_rejects : ¬ keyThree.A.plan.plan.samples = recordSet.samples + 1 := by
  decide +kernel

/-- **The premise on the number of answers, at the written values.** -/
theorem ha_of {made : Configured} {k : KeyChains}
    (q1 : k.oneTime.given.plan = keyThree.A.plan.plan) (hset : made.sized.set = recordSet) :
    k.oneTime.given.plan.samples = made.sized.set.samples := by
  rw [q1, hset]
  exact samples_written

end Johnson.KB9

#print axioms Johnson.KB9.samples_written
#print axioms Johnson.KB9.samples_rejects
#print axioms Johnson.KB9.ha_of
