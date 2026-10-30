-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsMerge.lean.
The routines of OnBytes/Model/Merge.lean keep what lies under the filled slots.

One statement for each routine: `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean)
or, for a routine of a link, `KeepsL` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine
takes routines as arguments, the statement has the premise that each of these has `Keeps`. Neither
property says anything of a run in which the routine refuses. Each statement is also given as a rule
to the tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsTsc
import OnBytes.Model.Merge

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model

theorem keeps_wsForkRounds : ∀ (a : ℕ) (r : Array E) (p : Psc),
    Keeps (OnBytes.Model.wsForkRounds a r p)
  | 0, r, p => by
    rw [OnBytes.Model.wsForkRounds]
    keeps
  | n + 1, r, p => by
    rw [OnBytes.Model.wsForkRounds]
    have ih := keeps_wsForkRounds n
    keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_wsForkRounds)

theorem keeps_Model_wsForkMerge (lk : Nat) (sv : Array Nat)  :
    Keeps (OnBytes.Model.wsForkMerge lk sv) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_wsForkMerge)

theorem keeps_Model_wsForkLin (o : WsMerged)  :
    Keeps (OnBytes.Model.wsForkLin o) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_wsForkLin)

theorem keeps_Model_wsForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat)  :
    Keeps (OnBytes.Model.wsForkEnd lay cl sv) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_wsForkEnd)

end Fo
