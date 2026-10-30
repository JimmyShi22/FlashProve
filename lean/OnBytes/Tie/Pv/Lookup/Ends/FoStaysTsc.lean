-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysTsc.lean.
Routines of OnBytes/Model/Tsc.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysTrees
import OnBytes.Model.Tsc

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model

theorem stays_tscLoop : ∀ (a : List E) (r : Array E) (p : Psc), DryS (OnBytes.Model.tscLoop a r p)
  | [], r, p => by
    rw [OnBytes.Model.tscLoop]
    stays
  | z :: zs, r, p => by
    rw [OnBytes.Model.tscLoop]
    have ih := stays_tscLoop zs
    stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_tscLoop)

theorem stays_Model_tscRounds (P : Array E) (lt : Nat)  :
    DryS (OnBytes.Model.tscRounds P lt) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_tscRounds)

theorem stays_Model_tscIn (P : Array E) (lt shown degreeInY : Nat)  :
    DryS (OnBytes.Model.tscIn P lt shown degreeInY) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_tscIn)

end Fo
