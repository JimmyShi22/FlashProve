-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsAttentionSums.lean.
The routines of OnBytes/Model/AttentionSums.lean keep what lies under the filled slots.

One statement for each routine: `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean)
or, for a routine of a link, `KeepsL` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine
takes routines as arguments, the statement has the premise that each of these has `Keeps`. Neither
property says anything of a run in which the routine refuses. Each statement is also given as a rule
to the tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsTail
import OnBytes.Model.AttentionSums

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Attention

theorem keeps_Attention_sc3Rounds  : ∀ (n : ℕ) (p : Model.Psc) (r : Array E),
    Keeps (OnBytes.Attention.sc3Rounds n p r)
  | 0, p, r => by
    rw [OnBytes.Attention.sc3Rounds]
    keeps
  | n + 1, p, r => by
    rw [OnBytes.Attention.sc3Rounds]
    have ih := keeps_Attention_sc3Rounds n
    keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_sc3Rounds)

theorem keeps_Attention_sc3Shown (o : Sc3) (W : Array E) : ∀ (n b : ℕ) (s : E),
    Keeps (OnBytes.Attention.sc3Shown o W n b s)
  | 0, b, s => by
    rw [OnBytes.Attention.sc3Shown]
    keeps
  | n + 1, b, s => by
    rw [OnBytes.Attention.sc3Shown]
    have ih := keeps_Attention_sc3Shown o W n
    keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_sc3Shown)

theorem keeps_Attention_scdRounds  : ∀ (ds : List ℕ) (p : Model.Psc) (r : Array E),
    Keeps (OnBytes.Attention.scdRounds ds p r)
  | [], p, r => by
    rw [OnBytes.Attention.scdRounds]
    keeps
  | d :: ds, p, r => by
    rw [OnBytes.Attention.scdRounds]
    have ih := keeps_Attention_scdRounds ds
    keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_scdRounds)

theorem keeps_Attention_sc3In (nv nb : Nat) (start : Model.Aff)  :
    Keeps (OnBytes.Attention.sc3In nv nb start) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_sc3In)

theorem keeps_Attention_sc3Row (o : Sc3) (W : Array E)  :
    Keeps (OnBytes.Attention.sc3Row o W) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_sc3Row)

theorem keeps_Attention_scdIn (degrees : List Nat) (degreeInY n : Nat) (start : Model.Aff)  :
    Keeps (OnBytes.Attention.scdIn degrees degreeInY n start) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_scdIn)

theorem keeps_Attention_scdRow (o : Scd) (s0 : E)  :
    Keeps (OnBytes.Attention.scdRow o s0) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_scdRow)

end Fo
