-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvHeadForms.lean.
The routines of OnBytes/Model/HeadForms.lean keep every property of the state that has `Prim`.

One statement a routine: `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a routine of a
link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvHeadTables
import OnBytes.Model.HeadForms

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem _root_.Fo.inv_Model_Head_segOf (R : Run) (sn : String)  :
    Inv I (OnBytes.Model.Head.segOf R sn) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_segOf)

theorem _root_.Fo.inv_Model_Head_ewOf (R : Run) (sn : String)  :
    Inv I (OnBytes.Model.Head.ewOf R sn) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_ewOf)

theorem _root_.Fo.inv_Model_Head_ewh (R : Run) (sn : String)  :
    Inv I (OnBytes.Model.Head.ewh R sn) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_ewh)

theorem _root_.Fo.inv_Model_Head_Sl (R : Run) (sn : String) (OFF nl J : Nat)  :
    Inv I (OnBytes.Model.Head.Sl R sn OFF nl J) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_Sl)

theorem _root_.Fo.inv_Model_Head_xbA (R : Run) (t kh : Nat)  :
    Inv I (OnBytes.Model.Head.xbA R t kh) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_xbA)

theorem _root_.Fo.inv_Model_Head_sh2 (R : Run) (t j : Nat)  :
    Inv I (OnBytes.Model.Head.sh2 R t j) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_sh2)

theorem _root_.Fo.inv_Model_Head_rowAt (R : Run) (P : String)  :
    Inv I (OnBytes.Model.Head.rowAt R P) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_rowAt)

theorem _root_.Fo.inv_Model_Head_row5At (R : Run) (P : String)  :
    Inv I (OnBytes.Model.Head.row5At R P) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_row5At)

theorem _root_.Fo.inv_Model_Head_gapAt (R : Run) (P : String) (i : Nat) (wsum : E)  :
    Inv I (OnBytes.Model.Head.gapAt R P i wsum) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_gapAt)

theorem _root_.Fo.inv_Model_Head_ztSeg (R : Run) (sn : String)  :
    Inv I (OnBytes.Model.Head.ztSeg R sn) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_ztSeg)

theorem _root_.Fo.inv_Model_Head_middleDigit (R : Run) (sn : String) (wR : E)  :
    Inv I (OnBytes.Model.Head.middleDigit R sn wR) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_middleDigit)

theorem _root_.Fo.inv_Model_Head_lowDigit (R : Run) (sn : String) (wR : E)  :
    Inv I (OnBytes.Model.Head.lowDigit R sn wR) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_lowDigit)

theorem _root_.Fo.inv_Model_Head_LINE (R : Run) (sn : String)  :
    Inv I (OnBytes.Model.Head.LINE R sn) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_LINE)

theorem _root_.Fo.inv_Model_Head_keyForm (R : Run) (q : Nat) (laid : Array Nat)  :
    Inv I (OnBytes.Model.Head.keyForm R q laid) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_keyForm)

end OnBytes.Model.Head
