-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsAttentionClaimsB.lean.
The routines of OnBytes/Model/AttentionClaimsB.lean keep what lies under the filled slots.

One statement for each routine: `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean)
or, for a routine of a link, `KeepsL` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine
takes routines as arguments, the statement has the premise that each of these has `Keeps`. Neither
property says anything of a run in which the routine refuses. Each statement is also given as a rule
to the tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsAttentionClaimsA
import OnBytes.Model.AttentionClaimsB

set_option autoImplicit false

namespace OnBytes.Attention
open Fo OnBytes.PscRun
open OnBytes.Model

theorem _root_.Fo.keeps_Attention_endValuesE (h : Heard) (b : Nat) (w : PW)  :
    Keeps (OnBytes.Attention.endValuesE h b w) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_endValuesE)

theorem _root_.Fo.keeps_Attention_claim5 (h : Heard) (j : Joins)  :
    Keeps (OnBytes.Attention.claim5 h j) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_claim5)

theorem _root_.Fo.keeps_Attention_valueProduct (h : Heard) (sc : Sc3) (tS : Nat) (pt : Array E) (isD
    : Bool) (tV : Nat)  :
    Keeps (OnBytes.Attention.valueProduct h sc tS pt isD tV) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Attention_valueProduct)

theorem _root_.Fo.keeps_Attention_claim6 (h : Heard)  :
    Keeps (OnBytes.Attention.claim6 h) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_claim6)

theorem _root_.Fo.keeps_Attention_claim7 (h : Heard)  :
    Keeps (OnBytes.Attention.claim7 h) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_claim7)

theorem _root_.Fo.keeps_Attention_claim8 (h : Heard)  :
    Keeps (OnBytes.Attention.claim8 h) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_claim8)

end OnBytes.Attention
