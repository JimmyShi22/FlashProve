-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsHeadForms.lean.
The routines of OnBytes/Model/HeadForms.lean keep what lies under the filled slots.

One statement for each routine: `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean)
or, for a routine of a link, `KeepsL` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine
takes routines as arguments, the statement has the premise that each of these has `Keeps`. Neither
property says anything of a run in which the routine refuses. Each statement is also given as a rule
to the tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsHeadTables
import OnBytes.Model.HeadForms

set_option autoImplicit false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

theorem _root_.Fo.keeps_Model_Head_segOf (R : Run) (sn : String)  :
    Keeps (OnBytes.Model.Head.segOf R sn) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_segOf)

theorem _root_.Fo.keeps_Model_Head_ewOf (R : Run) (sn : String)  :
    Keeps (OnBytes.Model.Head.ewOf R sn) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_ewOf)

theorem _root_.Fo.keeps_Model_Head_ewh (R : Run) (sn : String)  :
    Keeps (OnBytes.Model.Head.ewh R sn) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_ewh)

theorem _root_.Fo.keeps_Model_Head_Sl (R : Run) (sn : String) (OFF nl J : Nat)  :
    Keeps (OnBytes.Model.Head.Sl R sn OFF nl J) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_Sl)

theorem _root_.Fo.keeps_Model_Head_xbA (R : Run) (t kh : Nat)  :
    Keeps (OnBytes.Model.Head.xbA R t kh) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_xbA)

theorem _root_.Fo.keeps_Model_Head_sh2 (R : Run) (t j : Nat)  :
    Keeps (OnBytes.Model.Head.sh2 R t j) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_sh2)

theorem _root_.Fo.keeps_Model_Head_rowAt (R : Run) (P : String)  :
    Keeps (OnBytes.Model.Head.rowAt R P) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_rowAt)

theorem _root_.Fo.keeps_Model_Head_row5At (R : Run) (P : String)  :
    Keeps (OnBytes.Model.Head.row5At R P) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_row5At)

theorem _root_.Fo.keeps_Model_Head_gapAt (R : Run) (P : String) (i : Nat) (wsum : E)  :
    Keeps (OnBytes.Model.Head.gapAt R P i wsum) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_gapAt)

theorem _root_.Fo.keeps_Model_Head_ztSeg (R : Run) (sn : String)  :
    Keeps (OnBytes.Model.Head.ztSeg R sn) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_ztSeg)

theorem _root_.Fo.keeps_Model_Head_middleDigit (R : Run) (sn : String) (wR : E)  :
    Keeps (OnBytes.Model.Head.middleDigit R sn wR) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_middleDigit)

theorem _root_.Fo.keeps_Model_Head_lowDigit (R : Run) (sn : String) (wR : E)  :
    Keeps (OnBytes.Model.Head.lowDigit R sn wR) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_lowDigit)

theorem _root_.Fo.keeps_Model_Head_LINE (R : Run) (sn : String)  :
    Keeps (OnBytes.Model.Head.LINE R sn) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_LINE)

theorem _root_.Fo.keeps_Model_Head_keyForm (R : Run) (q : Nat) (laid : Array Nat)  :
    Keeps (OnBytes.Model.Head.keyForm R q laid) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_keyForm)

end OnBytes.Model.Head
