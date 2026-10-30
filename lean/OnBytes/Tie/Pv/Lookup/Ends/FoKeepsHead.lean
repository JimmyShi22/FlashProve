-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsHead.lean.
Routines of OnBytes/Model/Head.lean that keep what lies under the filled slots.

One statement for each routine but those that are left out (see below): `Keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean) or, for a routine of a link, `KeepsL`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine takes routines as arguments, the
statement has the premise that each of these has `Keeps`. Neither property says anything of a run in
which the routine refuses. Each statement is also given as a rule to the tactic `keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Left out: runForkHidH2, the sub-proof's whole check, which starts from a state without slots and
calls hear (OnBytes/Model/HeadHeard.lean), which sets the slots up anew, so that it does not keep
what lay under them (by reading; no theorem); selfTests, which calls HTailF2.coefficients (left out
of OnBytes/Tie/Pv/Lookup/Ends/FoKeepsTail.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsHeadForms
import OnBytes.Model.Head

set_option autoImplicit false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

theorem _root_.Fo.keeps_Model_Head_weightsClaim (R : Run) (wsLay : WsLay)  :
    Keeps (OnBytes.Model.Head.weightsClaim R wsLay) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_weightsClaim)

theorem _root_.Fo.keeps_Model_Head_claimSquares (R : Run)  :
    Keeps (OnBytes.Model.Head.claimSquares R) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_claimSquares)

theorem _root_.Fo.keeps_Model_Head_claimLedger5 (R : Run)  :
    Keeps (OnBytes.Model.Head.claimLedger5 R) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_claimLedger5)

theorem _root_.Fo.keeps_Model_Head_claimLedger4 (R : Run)  :
    Keeps (OnBytes.Model.Head.claimLedger4 R) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_claimLedger4)

theorem _root_.Fo.keeps_Model_Head_claimLedger (R : Run)  :
    Keeps (OnBytes.Model.Head.claimLedger R) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_claimLedger)

theorem _root_.Fo.keeps_Model_Head_claimStream (R : Run)  :
    Keeps (OnBytes.Model.Head.claimStream R) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_claimStream)

theorem _root_.Fo.keeps_Model_Head_claimJoin (R : Run)  :
    Keeps (OnBytes.Model.Head.claimJoin R) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_claimJoin)

theorem _root_.Fo.keeps_Model_Head_claimPolicy (R : Run)  :
    Keeps (OnBytes.Model.Head.claimPolicy R) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_claimPolicy)

theorem _root_.Fo.keeps_Model_Head_claimPlanes (R : Run)  :
    Keeps (OnBytes.Model.Head.claimPlanes R) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_claimPlanes)

theorem _root_.Fo.keeps_Model_Head_claimLogits (R : Run)  :
    Keeps (OnBytes.Model.Head.claimLogits R) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_claimLogits)

theorem _root_.Fo.keeps_Model_Head_noteConstant (group : String)  :
    Keeps (OnBytes.Model.Head.noteConstant group) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_noteConstant)

theorem _root_.Fo.keeps_Model_Head_walk (R : Run) (tl : HTailF2) (wo : WsForkOut)  :
    KeepsL (OnBytes.Model.Head.walk R tl wo) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_walk)

end OnBytes.Model.Head
