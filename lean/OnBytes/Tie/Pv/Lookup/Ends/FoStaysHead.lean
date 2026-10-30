-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysHead.lean.
Twelve routines of OnBytes/Model/Head.lean stay on the view: weightsClaim, claimSquares,
claimLedger5, claimLedger4, claimLedger, claimStream, claimJoin, claimPolicy, claimPlanes,
claimLogits, noteConstant; and walk, a routine of a link.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: from every state, a run on a view that returns is still on the view (`Dry`,
OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean: the mark of the dry run, false before, is false behind).
Nothing is said of a run that refuses, or of what a run reads. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysHeadForms
import OnBytes.Model.Head

set_option autoImplicit false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

theorem _root_.Fo.stays_Model_Head_weightsClaim (R : Run) (wsLay : WsLay)  :
    DryS (OnBytes.Model.Head.weightsClaim R wsLay) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_weightsClaim)

theorem _root_.Fo.stays_Model_Head_claimSquares (R : Run)  :
    DryS (OnBytes.Model.Head.claimSquares R) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_claimSquares)

theorem _root_.Fo.stays_Model_Head_claimLedger5 (R : Run)  :
    DryS (OnBytes.Model.Head.claimLedger5 R) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_claimLedger5)

theorem _root_.Fo.stays_Model_Head_claimLedger4 (R : Run)  :
    DryS (OnBytes.Model.Head.claimLedger4 R) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_claimLedger4)

theorem _root_.Fo.stays_Model_Head_claimLedger (R : Run)  :
    DryS (OnBytes.Model.Head.claimLedger R) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_claimLedger)

theorem _root_.Fo.stays_Model_Head_claimStream (R : Run)  :
    DryS (OnBytes.Model.Head.claimStream R) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_claimStream)

theorem _root_.Fo.stays_Model_Head_claimJoin (R : Run)  :
    DryS (OnBytes.Model.Head.claimJoin R) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_claimJoin)

theorem _root_.Fo.stays_Model_Head_claimPolicy (R : Run)  :
    DryS (OnBytes.Model.Head.claimPolicy R) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_claimPolicy)

theorem _root_.Fo.stays_Model_Head_claimPlanes (R : Run)  :
    DryS (OnBytes.Model.Head.claimPlanes R) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_claimPlanes)

theorem _root_.Fo.stays_Model_Head_claimLogits (R : Run)  :
    DryS (OnBytes.Model.Head.claimLogits R) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_claimLogits)

theorem _root_.Fo.stays_Model_Head_noteConstant (group : String)  :
    DryS (OnBytes.Model.Head.noteConstant group) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_noteConstant)

theorem _root_.Fo.stays_Model_Head_walk (R : Run) (tl : HTailF2) (wo : WsForkOut)  :
    DryL (OnBytes.Model.Head.walk R tl wo) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_walk)

end OnBytes.Model.Head
