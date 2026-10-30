-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvAttentionDivide.lean.
The routines of OnBytes/Model/AttentionDivide.lean keep every property of the state that has `Prim`.

One statement a routine: `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a routine of a
link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvAttentionScores
import OnBytes.Model.AttentionDivide

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Attention

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem inv_Attention_coinsOm (n : Nat)  :
    Inv I (OnBytes.Attention.coinsOm n) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_coinsOm)

theorem inv_Attention_productIn (S : Shape) (pwW : Array PW) (zgW ziW : Array E) (sZO : Nat)  :
    Inv I (OnBytes.Attention.productIn S pwW zgW ziW sZO) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_productIn)

theorem inv_Attention_valueBelowIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl : Nat) 
    :
    Inv I (OnBytes.Attention.valueBelowIn S pwW zgW zihi sCl) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_valueBelowIn)

theorem inv_Attention_valueOnIn (S : Shape) (pwW : Array PW) (zgW zihi : Array E) (sCl1 : Nat)  :
    Inv I (OnBytes.Attention.valueOnIn S pwW zgW zihi sCl1) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_valueOnIn)

theorem inv_Attention_divide (S : Shape) (zk : Array (Array E))  :
    Inv I (OnBytes.Attention.divide S zk) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_divide)

theorem inv_Attention_scoreAtIndexIn (S : Shape) (tg ti : Array E)  :
    Inv I (OnBytes.Attention.scoreAtIndexIn S tg ti) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Attention_scoreAtIndexIn)

theorem inv_Attention_keyTerm (S : Shape) (sKC : Nat) (pj : Array E) (w : E) (b : Nat)  :
    Inv I (OnBytes.Attention.keyTerm S sKC pj w b) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_keyTerm)

theorem inv_Attention_keyAtIndexIn (S : Shape) (scF : Sc3)  :
    Inv I (OnBytes.Attention.keyAtIndexIn S scF) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_keyAtIndexIn)

theorem inv_Attention_bitsIn (S : Shape) (tk tbg tbi : Array E)  :
    Inv I (OnBytes.Attention.bitsIn S tk tbg tbi) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_bitsIn)

theorem inv_Attention_attain (S : Shape)  :
    Inv I (OnBytes.Attention.attain S) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Attention_attain)

end Fo
