-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/KeyFirst.lean: the planner's first routine for a key file RETURNS at the typed
sizes of a key of full size, and returns the first written plan, FROM FOUR CLOSED FACTS: the run
alone returns; and the three parts of the plan's verdict accept the WRITTEN plan.

Why in parts. `Plan.oneTimePlan z` is `finish`, then the verdict `Planned.holds`, asked of the
rounds as the run leaves them. Asked whole of Lean's kernel, the check failed. But what the run
returns IS the written plan: by `finish_rounds` over `Plan.runs_oneTimeRounds` (its rounds are those
of a plain list) and `first_listed` (that list is the first written plan:
Johnson/Goal/Numbers/KeyFirstListed.lean). So the verdict may be asked of the written plan.

  `finish_of_run`: where the run returns, it returns the first written plan.
  `finishHeld_of`: a general law: where the run returns a plan that the verdict accepts,
    `finishHeld` returns it.
  `oneTime_of_four`: the four facts give `Plan.oneTimePlan keyFull = .ok keyThree.A.plan`.

Limits. THE FOUR FACTS ARE PREMISES HERE. No soundness is claimed.
-/
import Johnson.Goal.Numbers.KeyFirstListed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open VerifiableInference.Number.ByRuns OnBytes OnBytes.Params Lk6.AtPlan Johnson.G

/-- **Where the run returns, it returns the first written plan.** -/
theorem finish_of_run
    (ha : (finish keyFull.set .once (Plan.oneTimeRounds keyFull)).toOption.isSome = true) :
    finish keyFull.set .once (Plan.oneTimeRounds keyFull) = .ok keyThree.A.plan := by
  cases hf : finish keyFull.set .once (Plan.oneTimeRounds keyFull) with
  | error e =>
    rw [hf] at ha
    cases ha
  | ok P =>
    obtain ⟨e₁, e₂, _⟩ := finish_rounds (Plan.runs_oneTimeRounds keyFull) hf
    have e : P = firstListed := by
      obtain ⟨s, rs⟩ := P
      have e₁' : s = keyFull.set := e₁
      have e₂' : rs = (Plan.oneTimeList keyFull).map (·.round keyFull.set .once) := e₂
      rw [e₁', e₂']
      rfl
    rw [e, first_listed]

/-- Where the run returns a plan whose verdict is yes, `finishHeld` returns it. At letters. -/
theorem finishHeld_of {s : Setting} {c : Scope} {x : Planning Unit} {P : Planned}
    (hf : finish s c x = .ok P) (hh : P.holds = true) : finishHeld s c x = .ok P := by
  unfold finishHeld
  simp only [hf, hh, bind, Except.bind, if_true, pure, Except.pure]

/-- **Where the run returns and the three parts of the verdict accept the written plan (ha, h₁, h₂,
h₃: premises), the planner's first routine for a key file returns the first written plan.** -/
theorem oneTime_of_four
    (ha : (finish keyFull.set .once (Plan.oneTimeRounds keyFull)).toOption.isSome = true)
    (h₁ : keyThree.A.plan.roundsHold = true) (h₂ : keyThree.A.plan.wordsFit = true)
    (h₃ : keyThree.A.plan.oneDistance = true) :
    Plan.oneTimePlan keyFull = .ok keyThree.A.plan := by
  have hh : keyThree.A.plan.holds = true := by
    unfold Planned.holds
    rw [h₁, h₂, h₃]
    rfl
  unfold Plan.oneTimePlan
  exact finishHeld_of (finish_of_run ha) hh

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.finish_of_run
#print axioms Johnson.AtFull.Made.finishHeld_of
#print axioms Johnson.AtFull.Made.oneTime_of_four
