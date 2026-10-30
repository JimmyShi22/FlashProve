-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysHeadForms.lean.
Fourteen routines of OnBytes/Model/HeadForms.lean stay on the view: segOf, ewOf, ewh, Sl, xbA, sh2,
rowAt, row5At, gapAt, ztSeg, middleDigit, lowDigit, LINE, keyForm.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: from every state, a run on a view that returns is still on the view (`Dry`,
OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean: the mark of the dry run, false before, is false behind).
Nothing is said of a run that refuses, or of what a run reads. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysHeadTables
import OnBytes.Model.HeadForms

set_option autoImplicit false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

theorem _root_.Fo.stays_Model_Head_segOf (R : Run) (sn : String)  :
    DryS (OnBytes.Model.Head.segOf R sn) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_segOf)

theorem _root_.Fo.stays_Model_Head_ewOf (R : Run) (sn : String)  :
    DryS (OnBytes.Model.Head.ewOf R sn) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_ewOf)

theorem _root_.Fo.stays_Model_Head_ewh (R : Run) (sn : String)  :
    DryS (OnBytes.Model.Head.ewh R sn) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_ewh)

theorem _root_.Fo.stays_Model_Head_Sl (R : Run) (sn : String) (OFF nl J : Nat)  :
    DryS (OnBytes.Model.Head.Sl R sn OFF nl J) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_Sl)

theorem _root_.Fo.stays_Model_Head_xbA (R : Run) (t kh : Nat)  :
    DryS (OnBytes.Model.Head.xbA R t kh) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_xbA)

theorem _root_.Fo.stays_Model_Head_sh2 (R : Run) (t j : Nat)  :
    DryS (OnBytes.Model.Head.sh2 R t j) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_sh2)

theorem _root_.Fo.stays_Model_Head_rowAt (R : Run) (P : String)  :
    DryS (OnBytes.Model.Head.rowAt R P) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_rowAt)

theorem _root_.Fo.stays_Model_Head_row5At (R : Run) (P : String)  :
    DryS (OnBytes.Model.Head.row5At R P) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_row5At)

theorem _root_.Fo.stays_Model_Head_gapAt (R : Run) (P : String) (i : Nat) (wsum : E)  :
    DryS (OnBytes.Model.Head.gapAt R P i wsum) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_gapAt)

theorem _root_.Fo.stays_Model_Head_ztSeg (R : Run) (sn : String)  :
    DryS (OnBytes.Model.Head.ztSeg R sn) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_ztSeg)

theorem _root_.Fo.stays_Model_Head_middleDigit (R : Run) (sn : String) (wR : E)  :
    DryS (OnBytes.Model.Head.middleDigit R sn wR) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_middleDigit)

theorem _root_.Fo.stays_Model_Head_lowDigit (R : Run) (sn : String) (wR : E)  :
    DryS (OnBytes.Model.Head.lowDigit R sn wR) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_lowDigit)

theorem _root_.Fo.stays_Model_Head_LINE (R : Run) (sn : String)  :
    DryS (OnBytes.Model.Head.LINE R sn) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_LINE)

theorem _root_.Fo.stays_Model_Head_keyForm (R : Run) (q : Nat) (laid : Array Nat)  :
    DryS (OnBytes.Model.Head.keyForm R q laid) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_keyForm)

end OnBytes.Model.Head
