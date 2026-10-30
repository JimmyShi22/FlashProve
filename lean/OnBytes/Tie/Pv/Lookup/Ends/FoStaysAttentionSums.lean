-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysAttentionSums.lean.
Routines of OnBytes/Model/AttentionSums.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysTail
import OnBytes.Model.AttentionSums

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Attention

theorem stays_Attention_sc3Rounds  : ∀ (n : ℕ) (p : Model.Psc) (r : Array E),
    DryS (OnBytes.Attention.sc3Rounds n p r)
  | 0, p, r => by
    rw [OnBytes.Attention.sc3Rounds]
    stays
  | n + 1, p, r => by
    rw [OnBytes.Attention.sc3Rounds]
    have ih := stays_Attention_sc3Rounds n
    stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_sc3Rounds)

theorem stays_Attention_sc3Shown (o : Sc3) (W : Array E) : ∀ (n b : ℕ) (s : E),
    DryS (OnBytes.Attention.sc3Shown o W n b s)
  | 0, b, s => by
    rw [OnBytes.Attention.sc3Shown]
    stays
  | n + 1, b, s => by
    rw [OnBytes.Attention.sc3Shown]
    have ih := stays_Attention_sc3Shown o W n
    stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_sc3Shown)

theorem stays_Attention_scdRounds  : ∀ (ds : List ℕ) (p : Model.Psc) (r : Array E),
    DryS (OnBytes.Attention.scdRounds ds p r)
  | [], p, r => by
    rw [OnBytes.Attention.scdRounds]
    stays
  | d :: ds, p, r => by
    rw [OnBytes.Attention.scdRounds]
    have ih := stays_Attention_scdRounds ds
    stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_scdRounds)

theorem stays_Attention_sc3In (nv nb : Nat) (start : Model.Aff)  :
    DryS (OnBytes.Attention.sc3In nv nb start) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_sc3In)

theorem stays_Attention_sc3Row (o : Sc3) (W : Array E)  :
    DryS (OnBytes.Attention.sc3Row o W) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_sc3Row)

theorem stays_Attention_scdIn (degrees : List Nat) (degreeInY n : Nat) (start : Model.Aff)  :
    DryS (OnBytes.Attention.scdIn degrees degreeInY n start) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_scdIn)

theorem stays_Attention_scdRow (o : Scd) (s0 : E)  :
    DryS (OnBytes.Attention.scdRow o s0) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_scdRow)

end Fo
