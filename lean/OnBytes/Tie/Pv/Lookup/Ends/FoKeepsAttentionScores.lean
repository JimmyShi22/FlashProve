-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsAttentionScores.lean.
The routines of OnBytes/Model/AttentionScores.lean keep what lies under the filled slots.

One statement for each routine: `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean)
or, for a routine of a link, `KeepsL` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine
takes routines as arguments, the statement has the premise that each of these has `Keeps`. Neither
property says anything of a run in which the routine refuses. Each statement is also given as a rule
to the tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsAttentionSums
import OnBytes.Model.AttentionScores

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Attention

theorem keeps_Attention_planeUnit (S : Shape) (zk : Array (Array E)) (u : Nat × ACall × Seg)  :
    Keeps (OnBytes.Attention.planeUnit S zk u) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_planeUnit)

theorem keeps_Attention_planeUnits (S : Attention.Shape) (zk : Array (Array E)) : ∀
    (us : List (ℕ × ACall × Seg)) (pl : Array PlaneClaim),
        Keeps (OnBytes.Attention.planeUnits S zk us pl)
  | [], pl => by
    rw [OnBytes.Attention.planeUnits]
    keeps
  | u :: us, pl => by
    rw [OnBytes.Attention.planeUnits]
    have ih := keeps_Attention_planeUnits S zk us
    keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_planeUnits)

theorem keeps_Attention_scoreUnit (S : Shape) (zk : Array (Array E)) (claim : Nat) (u : Nat × ACall
    × Seg)  :
    Keeps (OnBytes.Attention.scoreUnit S zk claim u) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_scoreUnit)

theorem keeps_Attention_scoreUnits (S : Attention.Shape) (zk : Array (Array E)) : ∀ (us : List (ℕ ×
    ACall × Seg)) (pl : Array PlaneClaim) (st : Array Score), Keeps (OnBytes.Attention.scoreUnits S
    zk us pl st)
  | [], pl, st => by
    rw [OnBytes.Attention.scoreUnits]
    keeps
  | u :: us, pl, st => by
    rw [OnBytes.Attention.scoreUnits]
    have ih := keeps_Attention_scoreUnits S zk us
    keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_scoreUnits)

theorem keeps_Attention_scores (S : Shape) (zk : Array (Array E))  :
    Keeps (OnBytes.Attention.scores S zk) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_scores)

end Fo
