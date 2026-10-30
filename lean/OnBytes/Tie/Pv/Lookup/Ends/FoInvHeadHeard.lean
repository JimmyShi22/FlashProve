-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvHeadHeard.lean.
The routines of OnBytes/Model/HeadHeard.lean keep every property of the state that has `Prim`.

One statement a routine, but for those named under "Left out": `Inv I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a
routine of a link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Left out: Head.hear (no statement: it sets the slots up anew, or calls a routine that does).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvRange
import OnBytes.Model.HeadHeard

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OnBytes.Model.Head
open Fo OnBytes.PscRun

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem _root_.Fo.inv_Model_Head_noteH (what : String) (value : E)  :
    Inv I (OnBytes.Model.Head.noteH what value) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_noteH)

theorem _root_.Fo.inv_Model_Head_replyToken (plain : Array E) (V : Nat)  :
    Inv I (OnBytes.Model.Head.replyToken plain V) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_replyToken)

theorem _root_.Fo.inv_Model_Head_mergedPoint (h : Shape) (g1 : Forest.Heard)  :
    Inv I (OnBytes.Model.Head.mergedPoint h g1) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_mergedPoint)

theorem _root_.Fo.inv_Model_Head_hearSquares (h : Shape) (PV : Array E)  :
    Inv I (OnBytes.Model.Head.hearSquares h PV) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_hearSquares)

theorem _root_.Fo.inv_Model_Head_shownRun (first n : Nat)  :
    Inv I (OnBytes.Model.Head.shownRun first n) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Model_Head_shownRun)

theorem _root_.Fo.inv_Model_Head_hearProducts (h : Shape) (PV : Array E)  :
    Inv I (OnBytes.Model.Head.hearProducts h PV) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_hearProducts)

theorem _root_.Fo.inv_Model_Head_hearStream (h : Shape) (zt : Array E)  :
    Inv I (OnBytes.Model.Head.hearStream h zt) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_hearStream)

theorem _root_.Fo.inv_Head_channelRounds : ∀ (a : ℕ) (r : Array E) (p : Psc),
    Inv I (channelRounds a r p)
  | 0, r, p => by
    rw [channelRounds]
    inv
  | n + 1, r, p => by
    rw [channelRounds]
    have ih := Fo.inv_Head_channelRounds n
    inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Head_channelRounds)

theorem _root_.Fo.inv_Model_Head_hearLogits (h : Shape) (lam : Nat) (zt : Array E)  :
    Inv I (OnBytes.Model.Head.hearLogits h lam zt) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Model_Head_hearLogits)

end OnBytes.Model.Head
