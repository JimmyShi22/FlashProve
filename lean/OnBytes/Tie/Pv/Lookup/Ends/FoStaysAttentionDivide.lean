-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysAttentionDivide.lean.
Routines of OnBytes/Model/AttentionDivide.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysAttentionScores
import OnBytes.Model.AttentionDivide

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Attention

theorem stays_Attention_coinsOm (n : Nat)  :
    DryS (OnBytes.Attention.coinsOm n) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_coinsOm)

theorem stays_Attention_productIn (S : Shape) (pwW : Array PW) (zgW ziW : Array E) (sZO : Nat)  :
    DryS (OnBytes.Attention.productIn S pwW zgW ziW sZO) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_productIn)

theorem stays_Attention_valueBelowIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl : Nat) 
    :
    DryS (OnBytes.Attention.valueBelowIn S pwW zgW zihi sCl) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_valueBelowIn)

theorem stays_Attention_valueOnIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl1 : Nat)  :
    DryS (OnBytes.Attention.valueOnIn S pwW zgW zihi sCl1) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_valueOnIn)

theorem stays_Attention_divide (S : Shape) (zk : Array (Array E))  :
    DryS (OnBytes.Attention.divide S zk) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_divide)

theorem stays_Attention_scoreAtIndexIn (S : Shape) (tg ti : Array E)  :
    DryS (OnBytes.Attention.scoreAtIndexIn S tg ti) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Attention_scoreAtIndexIn)

theorem stays_Attention_keyTerm (S : Shape) (sKC : Nat) (pj : Array E) (w : E) (b : Nat)  :
    DryS (OnBytes.Attention.keyTerm S sKC pj w b) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_keyTerm)

theorem stays_Attention_keyAtIndexIn (S : Shape) (scF : Sc3)  :
    DryS (OnBytes.Attention.keyAtIndexIn S scF) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_keyAtIndexIn)

theorem stays_Attention_bitsIn (S : Shape) (tk tbg tbi : Array E)  :
    DryS (OnBytes.Attention.bitsIn S tk tbg tbi) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_bitsIn)

theorem stays_Attention_attain (S : Shape)  :
    DryS (OnBytes.Attention.attain S) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Attention_attain)

end Fo
