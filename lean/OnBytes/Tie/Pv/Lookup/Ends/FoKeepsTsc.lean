-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsTsc.lean.
The routines of OnBytes/Model/Tsc.lean keep what lies under the filled slots.

One statement for each routine: `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean)
or, for a routine of a link, `KeepsL` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine
takes routines as arguments, the statement has the premise that each of these has `Keeps`. Neither
property says anything of a run in which the routine refuses. Each statement is also given as a rule
to the tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsTrees
import OnBytes.Model.Tsc

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model

theorem keeps_tscLoop : ∀ (a : List E) (r : Array E) (p : Psc), Keeps (OnBytes.Model.tscLoop a r p)
  | [], r, p => by
    rw [OnBytes.Model.tscLoop]
    keeps
  | z :: zs, r, p => by
    rw [OnBytes.Model.tscLoop]
    have ih := keeps_tscLoop zs
    keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_tscLoop)

theorem keeps_Model_tscRounds (P : Array E) (lt : Nat)  :
    Keeps (OnBytes.Model.tscRounds P lt) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_tscRounds)

theorem keeps_Model_tscIn (P : Array E) (lt shown degreeInY : Nat)  :
    Keeps (OnBytes.Model.tscIn P lt shown degreeInY) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_tscIn)

end Fo
