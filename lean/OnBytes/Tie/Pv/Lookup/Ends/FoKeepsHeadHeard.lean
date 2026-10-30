-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsHeadHeard.lean.
Routines of OnBytes/Model/HeadHeard.lean that keep what lies under the filled slots.

One statement for each routine but those that are left out (see below): `Keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean) or, for a routine of a link, `KeepsL`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine takes routines as arguments, the
statement has the premise that each of these has `Keeps`. Neither property says anything of a run in
which the routine refuses. Each statement is also given as a rule to the tactic `keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Left out: hear, which sets up the slots anew (SubM.slots) and so does not keep what lay under them
(by reading; no theorem).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsRange
import OnBytes.Model.HeadHeard

set_option autoImplicit false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

theorem _root_.Fo.keeps_Model_Head_noteH (what : String) (value : E)  :
    Keeps (OnBytes.Model.Head.noteH what value) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_noteH)

theorem _root_.Fo.keeps_Model_Head_replyToken (plain : Array E) (V : Nat)  :
    Keeps (OnBytes.Model.Head.replyToken plain V) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_replyToken)

theorem _root_.Fo.keeps_Model_Head_mergedPoint (h : Shape) (g1 : Forest.Heard)  :
    Keeps (OnBytes.Model.Head.mergedPoint h g1) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_mergedPoint)

theorem _root_.Fo.keeps_Model_Head_hearSquares (h : Shape) (PV : Array E)  :
    Keeps (OnBytes.Model.Head.hearSquares h PV) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_hearSquares)

theorem _root_.Fo.keeps_Model_Head_shownRun (first n : Nat)  :
    Keeps (OnBytes.Model.Head.shownRun first n) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Model_Head_shownRun)

theorem _root_.Fo.keeps_Model_Head_hearProducts (h : Shape) (PV : Array E)  :
    Keeps (OnBytes.Model.Head.hearProducts h PV) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_hearProducts)

theorem _root_.Fo.keeps_Model_Head_hearStream (h : Shape) (zt : Array E)  :
    Keeps (OnBytes.Model.Head.hearStream h zt) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_hearStream)

theorem _root_.Fo.keeps_Head_channelRounds : ∀ (a : ℕ) (r : Array E) (p : Psc),
    Keeps (channelRounds a r p)
  | 0, r, p => by
    rw [channelRounds]
    keeps
  | n + 1, r, p => by
    rw [channelRounds]
    have ih := Fo.keeps_Head_channelRounds n
    keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Head_channelRounds)

theorem _root_.Fo.keeps_Model_Head_hearLogits (h : Shape) (lam : Nat) (zt : Array E)  :
    Keeps (OnBytes.Model.Head.hearLogits h lam zt) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Model_Head_hearLogits)

end OnBytes.Model.Head
