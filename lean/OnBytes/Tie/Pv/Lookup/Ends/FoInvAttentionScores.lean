-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvAttentionScores.lean.
The routines of OnBytes/Model/AttentionScores.lean keep every property of the state that has `Prim`.

One statement a routine: `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a routine of a
link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvAttentionSums
import OnBytes.Model.AttentionScores

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Attention

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem inv_Attention_planeUnit (S : Shape) (zk : Array (Array E)) (u : Nat × ACall × Seg)  :
    Inv I (OnBytes.Attention.planeUnit S zk u) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_planeUnit)

theorem inv_Attention_planeUnits (S : Attention.Shape) (zk : Array (Array E)) : ∀
    (us : List (ℕ × ACall × Seg)) (pl : Array PlaneClaim),
        Inv I (OnBytes.Attention.planeUnits S zk us pl)
  | [], pl => by
    rw [OnBytes.Attention.planeUnits]
    inv
  | u :: us, pl => by
    rw [OnBytes.Attention.planeUnits]
    have ih := inv_Attention_planeUnits S zk us
    inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_planeUnits)

theorem inv_Attention_scoreUnit (S : Shape) (zk : Array (Array E)) (claim : Nat) (u : Nat × ACall
    × Seg)  :
    Inv I (OnBytes.Attention.scoreUnit S zk claim u) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_scoreUnit)

theorem inv_Attention_scoreUnits (S : Attention.Shape) (zk : Array (Array E)) : ∀ (us : List (ℕ ×
    ACall × Seg)) (pl : Array PlaneClaim) (st : Array Score), Inv I (OnBytes.Attention.scoreUnits S
    zk us pl st)
  | [], pl, st => by
    rw [OnBytes.Attention.scoreUnits]
    inv
  | u :: us, pl, st => by
    rw [OnBytes.Attention.scoreUnits]
    have ih := inv_Attention_scoreUnits S zk us
    inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_scoreUnits)

theorem inv_Attention_scores (S : Shape) (zk : Array (Array E))  :
    Inv I (OnBytes.Attention.scores S zk) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_scores)

end Fo
