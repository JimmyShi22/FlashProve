-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysAttentionClaimsB.lean.
Routines of OnBytes/Model/AttentionClaimsB.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysAttentionClaimsA
import OnBytes.Model.AttentionClaimsB

set_option autoImplicit false

namespace OnBytes.Attention
open Fo OnBytes.PscRun
open OnBytes.Model

theorem _root_.Fo.stays_Attention_endValuesE (h : Heard) (b : Nat) (w : PW)  :
    DryS (OnBytes.Attention.endValuesE h b w) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_endValuesE)

theorem _root_.Fo.stays_Attention_claim5 (h : Heard) (j : Joins)  :
    DryS (OnBytes.Attention.claim5 h j) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_claim5)

theorem _root_.Fo.stays_Attention_valueProduct (h : Heard) (sc : Sc3) (tS : Nat) (pt : Array E) (isD
    : Bool) (tV : Nat)  :
    DryS (OnBytes.Attention.valueProduct h sc tS pt isD tV) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Attention_valueProduct)

theorem _root_.Fo.stays_Attention_claim6 (h : Heard)  :
    DryS (OnBytes.Attention.claim6 h) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_claim6)

theorem _root_.Fo.stays_Attention_claim7 (h : Heard)  :
    DryS (OnBytes.Attention.claim7 h) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_claim7)

theorem _root_.Fo.stays_Attention_claim8 (h : Heard)  :
    DryS (OnBytes.Attention.claim8 h) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_claim8)

end OnBytes.Attention
