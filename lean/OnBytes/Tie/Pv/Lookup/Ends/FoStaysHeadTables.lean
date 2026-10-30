-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysHeadTables.lean.
Three routines of OnBytes/Model/HeadTables.lean stay on the view: tablesOf, tabAt, U3at.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: from every state, a run on a view that returns is still on the view (`Dry`,
OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean: the mark of the dry run, false before, is false behind).
Nothing is said of a run that refuses, or of what a run reads. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysHeadHeard
import OnBytes.Model.HeadTables

set_option autoImplicit false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

theorem _root_.Fo.stays_Model_Head_tablesOf (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x :
    Heard)  :
    DryS (OnBytes.Model.Head.tablesOf h L hp cov x) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_tablesOf)

theorem _root_.Fo.stays_Model_Head_tabAt (R : Run) (n : String)  :
    DryS (OnBytes.Model.Head.tabAt R n) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_tabAt)

theorem _root_.Fo.stays_Model_Head_U3at (R : Run) (t i : Nat)  :
    DryS (OnBytes.Model.Head.U3at R t i) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_U3at)

end OnBytes.Model.Head
