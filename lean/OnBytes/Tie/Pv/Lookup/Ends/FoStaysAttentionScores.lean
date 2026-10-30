-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysAttentionScores.lean.
Routines of OnBytes/Model/AttentionScores.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysAttentionSums
import OnBytes.Model.AttentionScores

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Attention

theorem stays_Attention_planeUnit (S : Shape) (zk : Array (Array E)) (u : Nat × ACall × Seg)  :
    DryS (OnBytes.Attention.planeUnit S zk u) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_planeUnit)

theorem stays_Attention_planeUnits (S : Attention.Shape) (zk : Array (Array E)) : ∀
    (us : List (ℕ × ACall × Seg)) (pl : Array PlaneClaim),
        DryS (OnBytes.Attention.planeUnits S zk us pl)
  | [], pl => by
    rw [OnBytes.Attention.planeUnits]
    stays
  | u :: us, pl => by
    rw [OnBytes.Attention.planeUnits]
    have ih := stays_Attention_planeUnits S zk us
    stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_planeUnits)

theorem stays_Attention_scoreUnit (S : Shape) (zk : Array (Array E)) (claim : Nat) (u : Nat × ACall
    × Seg)  :
    DryS (OnBytes.Attention.scoreUnit S zk claim u) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_scoreUnit)

theorem stays_Attention_scoreUnits (S : Attention.Shape) (zk : Array (Array E)) : ∀ (us : List (ℕ ×
    ACall × Seg)) (pl : Array PlaneClaim) (st : Array Score), DryS (OnBytes.Attention.scoreUnits S
    zk us pl st)
  | [], pl, st => by
    rw [OnBytes.Attention.scoreUnits]
    stays
  | u :: us, pl, st => by
    rw [OnBytes.Attention.scoreUnits]
    have ih := stays_Attention_scoreUnits S zk us
    stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_scoreUnits)

theorem stays_Attention_scores (S : Shape) (zk : Array (Array E))  :
    DryS (OnBytes.Attention.scores S zk) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_scores)

end Fo
