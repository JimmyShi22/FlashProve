-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/OfRuns.lean: from a routine's list of rounds to the value of the finished plan.
A general law on the planner (OnBytes/Params/Planner.lean): no written value, no evaluation. A law
file; no running text imports it.

`Runs` (OnBytes/Params/PlanningLaws.lean) says what a routine adds WHERE it ends well: its value,
the rounds of a plain list, the three open counts. So of the run itself one bit alone is still
wanted: that it ends well.

Statements.
  `finishHeld_of_runs`: if x adds the rounds of l from nothing open to nothing open, x ends well
    from the empty plan (`Except.isOk`), and the plan of l's rounds passes the planner's verdict
    (`Planned.holds`), then `finishHeld s c x` returns that plan.

Limits. A conditional: it shows of no routine that it ends well. Nothing on what a round means.
Nothing on soundness.
-/
import OnBytes.Params.PlanningLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params

/-- **The finished plan, as a value.** -/
theorem finishHeld_of_runs {s : Setting} {c : Scope} {x : Planning Unit} {l : List RoundSpec}
    (hx : Runs s c 0 0 0 x () l 0 0 0)
    (hr : (x { set := s, scope := c }).isOk = true)
    (hh : (⟨s, l.map (·.round s c)⟩ : Planned).holds = true) :
    finishHeld s c x = .ok ⟨s, l.map (·.round s c)⟩ := by
  cases hp : x { set := s, scope := c } with
  | error e =>
    rw [hp] at hr
    cases hr
  | ok v =>
    obtain ⟨u, p⟩ := v
    obtain ⟨_, _, _, q, b, r, a, _⟩ := hx _ p u rfl rfl rfl rfl rfl hp
    have q' : p.rounds.toList = l.map (·.round s c) := by simpa using q
    have hf : finish s c x = .ok ⟨s, l.map (·.round s c)⟩ := by
      unfold finish
      rw [hp]
      simp only [b, r, a, q', bne_self_eq_false, Bool.or_self, Bool.false_eq_true, if_false]
    unfold finishHeld
    rw [hf]
    show (if (⟨s, l.map (·.round s c)⟩ : Planned).holds = true then
      (pure ⟨s, l.map (·.round s c)⟩ : Except String Planned) else throw notAdmitted) = _
    rw [if_pos hh]
    rfl

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.finishHeld_of_runs
