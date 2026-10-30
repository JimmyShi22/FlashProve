-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvHeadTables.lean.
The routines of OnBytes/Model/HeadTables.lean keep every property of the state that has `Prim`.

One statement a routine: `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a routine of a
link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvHeadHeard
import OnBytes.Model.HeadTables

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem _root_.Fo.inv_Model_Head_tablesOf (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x :
    Heard)  :
    Inv I (OnBytes.Model.Head.tablesOf h L hp cov x) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_tablesOf)

theorem _root_.Fo.inv_Model_Head_tabAt (R : Run) (n : String)  :
    Inv I (OnBytes.Model.Head.tabAt R n) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_tabAt)

theorem _root_.Fo.inv_Model_Head_U3at (R : Run) (t i : Nat)  :
    Inv I (OnBytes.Model.Head.U3at R t i) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_U3at)

end OnBytes.Model.Head
