-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsAttentionDivide.lean.
The routines of OnBytes/Model/AttentionDivide.lean keep what lies under the filled slots.

One statement for each routine: `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean)
or, for a routine of a link, `KeepsL` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine
takes routines as arguments, the statement has the premise that each of these has `Keeps`. Neither
property says anything of a run in which the routine refuses. Each statement is also given as a rule
to the tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsAttentionScores
import OnBytes.Model.AttentionDivide

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Attention

theorem keeps_Attention_coinsOm (n : Nat)  :
    Keeps (OnBytes.Attention.coinsOm n) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_coinsOm)

theorem keeps_Attention_productIn (S : Shape) (pwW : Array PW) (zgW ziW : Array E) (sZO : Nat)  :
    Keeps (OnBytes.Attention.productIn S pwW zgW ziW sZO) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_productIn)

theorem keeps_Attention_valueBelowIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl : Nat) 
    :
    Keeps (OnBytes.Attention.valueBelowIn S pwW zgW zihi sCl) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_valueBelowIn)

theorem keeps_Attention_valueOnIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl1 : Nat)  :
    Keeps (OnBytes.Attention.valueOnIn S pwW zgW zihi sCl1) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_valueOnIn)

theorem keeps_Attention_divide (S : Shape) (zk : Array (Array E))  :
    Keeps (OnBytes.Attention.divide S zk) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_divide)

theorem keeps_Attention_scoreAtIndexIn (S : Shape) (tg ti : Array E)  :
    Keeps (OnBytes.Attention.scoreAtIndexIn S tg ti) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Attention_scoreAtIndexIn)

theorem keeps_Attention_keyTerm (S : Shape) (sKC : Nat) (pj : Array E) (w : E) (b : Nat)  :
    Keeps (OnBytes.Attention.keyTerm S sKC pj w b) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_keyTerm)

theorem keeps_Attention_keyAtIndexIn (S : Shape) (scF : Sc3)  :
    Keeps (OnBytes.Attention.keyAtIndexIn S scF) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_keyAtIndexIn)

theorem keeps_Attention_bitsIn (S : Shape) (tk tbg tbi : Array E)  :
    Keeps (OnBytes.Attention.bitsIn S tk tbg tbi) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_bitsIn)

theorem keeps_Attention_attain (S : Shape)  :
    Keeps (OnBytes.Attention.attain S) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Attention_attain)

end Fo
