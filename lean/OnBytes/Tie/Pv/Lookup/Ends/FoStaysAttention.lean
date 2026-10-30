-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysAttention.lean.
Routines of OnBytes/Model/Attention.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.
Left out of that file's routines: `Seam.start`, `Seam.finish` and `run`; the statement on `run` is
`staysL_runA` (OnBytes/Tie/Pv/Lookup/Ends/FoStaysTop.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysAttentionClaimsB
import OnBytes.Model.Attention

set_option autoImplicit false

namespace OnBytes.Attention.Seam
open Fo OnBytes.PscRun
open OnBytes.Model

theorem _root_.Fo.stays_Attention_Seam_transcript (tl : HTailF2)  :
    DryL (OnBytes.Attention.Seam.transcript tl) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Attention_Seam_transcript)

theorem _root_.Fo.stays_Attention_Seam_batch (used : Nat)  :
    DryL (OnBytes.Attention.Seam.batch used) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_Seam_batch)

theorem _root_.Fo.stays_Attention_Seam_objects (tl : HTailF2) (funs : Array HFun)  :
    DryS (OnBytes.Attention.Seam.objects tl funs) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Attention_Seam_objects)

end OnBytes.Attention.Seam

namespace OnBytes.Attention
open Fo OnBytes.PscRun
open OnBytes.Model

theorem _root_.Fo.stays_Attention_allJoined (j : Joins)  :
    DryS (OnBytes.Attention.allJoined j) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_allJoined)

theorem _root_.Fo.stays_Attention_paddingLaid (S : Shape) (g : Forest.Heard)  :
    DryS (OnBytes.Attention.paddingLaid S g) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Attention_paddingLaid)

theorem _root_.Fo.stays_Attention_noFreeSlot (nMsg : Nat)  :
    DryS (OnBytes.Attention.noFreeSlot nMsg) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_noFreeSlot)

theorem _root_.Fo.stays_Attention_countsHeld (P : Plan) (tl : HTailF2)  :
    DryS (OnBytes.Attention.countsHeld P tl) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_countsHeld)

theorem _root_.Fo.stays_Attention_hear (P : Plan)  :
    DryS (OnBytes.Attention.hear P) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_hear)

theorem _root_.Fo.stays_Attention_claims (P : Plan) (h : Heard)  :
    DryS (OnBytes.Attention.claims P h) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_claims)

end OnBytes.Attention
