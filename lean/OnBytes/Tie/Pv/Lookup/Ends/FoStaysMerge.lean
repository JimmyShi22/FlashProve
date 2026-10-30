-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysMerge.lean.
Routines of OnBytes/Model/Merge.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysTsc
import OnBytes.Model.Merge

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model

theorem stays_wsForkRounds : ∀ (a : ℕ) (r : Array E) (p : Psc),
    DryS (OnBytes.Model.wsForkRounds a r p)
  | 0, r, p => by
    rw [OnBytes.Model.wsForkRounds]
    stays
  | n + 1, r, p => by
    rw [OnBytes.Model.wsForkRounds]
    have ih := stays_wsForkRounds n
    stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_wsForkRounds)

theorem stays_Model_wsForkMerge (lk : Nat) (sv : Array Nat)  :
    DryS (OnBytes.Model.wsForkMerge lk sv) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_wsForkMerge)

theorem stays_Model_wsForkLin (o : WsMerged)  :
    DryS (OnBytes.Model.wsForkLin o) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_wsForkLin)

theorem stays_Model_wsForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat)  :
    DryS (OnBytes.Model.wsForkEnd lay cl sv) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_wsForkEnd)

end Fo
