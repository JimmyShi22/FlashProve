-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvHead.lean.
The routines of OnBytes/Model/Head.lean keep every property of the state that has `Prim`.

One statement a routine, but for those named under "Left out": `Inv I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a
routine of a link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Left out: Head.runForkHidH2 (no statement: it sets the slots up anew, or calls a routine that does);
Head.selfTests (OnBytes/Tie/Pv/Lookup/Ends/FoInvCoef.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvHeadForms
import OnBytes.Model.Head

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem _root_.Fo.inv_Model_Head_weightsClaim (R : Run) (wsLay : WsLay)  :
    Inv I (OnBytes.Model.Head.weightsClaim R wsLay) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_weightsClaim)

theorem _root_.Fo.inv_Model_Head_claimSquares (R : Run)  :
    Inv I (OnBytes.Model.Head.claimSquares R) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_claimSquares)

theorem _root_.Fo.inv_Model_Head_claimLedger5 (R : Run)  :
    Inv I (OnBytes.Model.Head.claimLedger5 R) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_claimLedger5)

theorem _root_.Fo.inv_Model_Head_claimLedger4 (R : Run)  :
    Inv I (OnBytes.Model.Head.claimLedger4 R) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_claimLedger4)

theorem _root_.Fo.inv_Model_Head_claimLedger (R : Run)  :
    Inv I (OnBytes.Model.Head.claimLedger R) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_claimLedger)

theorem _root_.Fo.inv_Model_Head_claimStream (R : Run)  :
    Inv I (OnBytes.Model.Head.claimStream R) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_claimStream)

theorem _root_.Fo.inv_Model_Head_claimJoin (R : Run)  :
    Inv I (OnBytes.Model.Head.claimJoin R) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_claimJoin)

theorem _root_.Fo.inv_Model_Head_claimPolicy (R : Run)  :
    Inv I (OnBytes.Model.Head.claimPolicy R) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_claimPolicy)

theorem _root_.Fo.inv_Model_Head_claimPlanes (R : Run)  :
    Inv I (OnBytes.Model.Head.claimPlanes R) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_claimPlanes)

theorem _root_.Fo.inv_Model_Head_claimLogits (R : Run)  :
    Inv I (OnBytes.Model.Head.claimLogits R) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_claimLogits)

theorem _root_.Fo.inv_Model_Head_noteConstant (group : String)  :
    Inv I (OnBytes.Model.Head.noteConstant group) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_noteConstant)

theorem _root_.Fo.inv_Model_Head_walk (R : Run) (tl : HTailF2) (wo : WsForkOut)  :
    InvL I (OnBytes.Model.Head.walk R tl wo) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_walk)

end OnBytes.Model.Head
