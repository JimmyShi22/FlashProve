-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsAttention.lean.
Routines of OnBytes/Model/Attention.lean that keep what lies under the filled slots.

One statement for each routine but those that are left out (see below): `Keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean) or, for a routine of a link, `KeepsL`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine takes routines as arguments, the
statement has the premise that each of these has `Keeps`. Neither property says anything of a run in
which the routine refuses. Each statement is also given as a rule to the tactic `keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Left out: Seam.start, which sets up the slots anew (Fork.slots) and so does not keep what lay under
them (by reading; no theorem); run, the sub-proof's whole check, which calls it; Seam.finish, which
calls HTailF2.coefficients (left out of OnBytes/Tie/Pv/Lookup/Ends/FoKeepsTail.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsAttentionClaimsB
import OnBytes.Model.Attention

set_option autoImplicit false

namespace OnBytes.Attention.Seam
open Fo OnBytes.PscRun
open OnBytes.Model

theorem _root_.Fo.keeps_Attention_Seam_transcript (tl : HTailF2)  :
    KeepsL (OnBytes.Attention.Seam.transcript tl) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Attention_Seam_transcript)

theorem _root_.Fo.keeps_Attention_Seam_batch (used : Nat)  :
    KeepsL (OnBytes.Attention.Seam.batch used) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_Seam_batch)

theorem _root_.Fo.keeps_Attention_Seam_objects (tl : HTailF2) (funs : Array HFun)  :
    Keeps (OnBytes.Attention.Seam.objects tl funs) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Attention_Seam_objects)

end OnBytes.Attention.Seam

namespace OnBytes.Attention
open Fo OnBytes.PscRun
open OnBytes.Model

theorem _root_.Fo.keeps_Attention_allJoined (j : Joins)  :
    Keeps (OnBytes.Attention.allJoined j) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_allJoined)

theorem _root_.Fo.keeps_Attention_paddingLaid (S : Shape) (g : Forest.Heard)  :
    Keeps (OnBytes.Attention.paddingLaid S g) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Attention_paddingLaid)

theorem _root_.Fo.keeps_Attention_noFreeSlot (nMsg : Nat)  :
    Keeps (OnBytes.Attention.noFreeSlot nMsg) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_noFreeSlot)

theorem _root_.Fo.keeps_Attention_countsHeld (P : Plan) (tl : HTailF2)  :
    Keeps (OnBytes.Attention.countsHeld P tl) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_countsHeld)

theorem _root_.Fo.keeps_Attention_hear (P : Plan)  :
    Keeps (OnBytes.Attention.hear P) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_hear)

theorem _root_.Fo.keeps_Attention_claims (P : Plan) (h : Heard)  :
    Keeps (OnBytes.Attention.claims P h) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_claims)

end OnBytes.Attention
