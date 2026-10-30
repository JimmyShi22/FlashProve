-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysHeadHeard.lean.
Nine routines of OnBytes/Model/HeadHeard.lean stay on the view: noteH, replyToken, mergedPoint,
hearSquares, shownRun, hearProducts, hearStream, channelRounds, hearLogits.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: from every state, a run on a view that returns is still on the view (`Dry`,
OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean: the mark of the dry run, false before, is false behind).
Nothing is said of a run that refuses, or of what a run reads. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body. channelRounds is defined
by recursion: its proof goes by induction, with `stays` in each case.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysRange
import OnBytes.Model.HeadHeard

set_option autoImplicit false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

theorem _root_.Fo.stays_Model_Head_noteH (what : String) (value : E)  :
    DryS (OnBytes.Model.Head.noteH what value) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_noteH)

theorem _root_.Fo.stays_Model_Head_replyToken (plain : Array E) (V : Nat)  :
    DryS (OnBytes.Model.Head.replyToken plain V) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_replyToken)

theorem _root_.Fo.stays_Model_Head_mergedPoint (h : Shape) (g1 : Forest.Heard)  :
    DryS (OnBytes.Model.Head.mergedPoint h g1) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_mergedPoint)

theorem _root_.Fo.stays_Model_Head_hearSquares (h : Shape) (PV : Array E)  :
    DryS (OnBytes.Model.Head.hearSquares h PV) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_hearSquares)

theorem _root_.Fo.stays_Model_Head_shownRun (first n : Nat)  :
    DryS (OnBytes.Model.Head.shownRun first n) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Model_Head_shownRun)

theorem _root_.Fo.stays_Model_Head_hearProducts (h : Shape) (PV : Array E)  :
    DryS (OnBytes.Model.Head.hearProducts h PV) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_hearProducts)

theorem _root_.Fo.stays_Model_Head_hearStream (h : Shape) (zt : Array E)  :
    DryS (OnBytes.Model.Head.hearStream h zt) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_hearStream)

theorem _root_.Fo.stays_Head_channelRounds : ∀ (a : ℕ) (r : Array E) (p : Psc),
    DryS (channelRounds a r p)
  | 0, r, p => by
    rw [channelRounds]
    stays
  | n + 1, r, p => by
    rw [channelRounds]
    have ih := Fo.stays_Head_channelRounds n
    stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Head_channelRounds)

theorem _root_.Fo.stays_Model_Head_hearLogits (h : Shape) (lam : Nat) (zt : Array E)  :
    DryS (OnBytes.Model.Head.hearLogits h lam zt) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Model_Head_hearLogits)

end OnBytes.Model.Head
