-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvAttentionClaimsB.lean.
The routines of OnBytes/Model/AttentionClaimsB.lean keep every property of the state that has
`Prim`.

One statement a routine: `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a routine of a
link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvAttentionClaimsA
import OnBytes.Model.AttentionClaimsB

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OnBytes.Attention
open Fo OnBytes.PscRun
open OnBytes.Model

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem _root_.Fo.inv_Attention_endValuesE (h : Heard) (b : Nat) (w : PW)  :
    Inv I (OnBytes.Attention.endValuesE h b w) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_endValuesE)

theorem _root_.Fo.inv_Attention_claim5 (h : Heard) (j : Joins)  :
    Inv I (OnBytes.Attention.claim5 h j) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_claim5)

theorem _root_.Fo.inv_Attention_valueProduct (h : Heard) (sc : Sc3) (tS : Nat) (pt : Array E) (isD
    : Bool) (tV : Nat)  :
    Inv I (OnBytes.Attention.valueProduct h sc tS pt isD tV) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Attention_valueProduct)

theorem _root_.Fo.inv_Attention_claim6 (h : Heard)  :
    Inv I (OnBytes.Attention.claim6 h) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_claim6)

theorem _root_.Fo.inv_Attention_claim7 (h : Heard)  :
    Inv I (OnBytes.Attention.claim7 h) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_claim7)

theorem _root_.Fo.inv_Attention_claim8 (h : Heard)  :
    Inv I (OnBytes.Attention.claim8 h) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_claim8)

end OnBytes.Attention
