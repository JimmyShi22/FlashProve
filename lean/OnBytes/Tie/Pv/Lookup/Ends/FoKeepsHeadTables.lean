-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsHeadTables.lean.
The routines of OnBytes/Model/HeadTables.lean keep what lies under the filled slots.

One statement for each routine: `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean)
or, for a routine of a link, `KeepsL` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine
takes routines as arguments, the statement has the premise that each of these has `Keeps`. Neither
property says anything of a run in which the routine refuses. Each statement is also given as a rule
to the tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsHeadHeard
import OnBytes.Model.HeadTables

set_option autoImplicit false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

theorem _root_.Fo.keeps_Model_Head_tablesOf (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x :
    Heard)  :
    Keeps (OnBytes.Model.Head.tablesOf h L hp cov x) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_tablesOf)

theorem _root_.Fo.keeps_Model_Head_tabAt (R : Run) (n : String)  :
    Keeps (OnBytes.Model.Head.tabAt R n) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_tabAt)

theorem _root_.Fo.keeps_Model_Head_U3at (R : Run) (t i : Nat)  :
    Keeps (OnBytes.Model.Head.U3at R t i) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_U3at)

end OnBytes.Model.Head
