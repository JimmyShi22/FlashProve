-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvAttention.lean.
The routines of OnBytes/Model/Attention.lean keep every property of the state that has `Prim`.

One statement a routine, but for those named under "Left out": `Inv I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a
routine of a link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Left out: Attention.Seam.start, Attention.run (no statement: it sets the slots up anew, or calls a
routine that does); Attention.Seam.finish
(OnBytes/Tie/Pv/Lookup/Ends/FoInvCoef.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvAttentionClaimsB
import OnBytes.Model.Attention

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OnBytes.Attention.Seam
open Fo OnBytes.PscRun
open OnBytes.Model

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem _root_.Fo.inv_Attention_Seam_transcript (tl : HTailF2)  :
    InvL I (OnBytes.Attention.Seam.transcript tl) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Attention_Seam_transcript)

theorem _root_.Fo.inv_Attention_Seam_batch (used : Nat)  :
    InvL I (OnBytes.Attention.Seam.batch used) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_Seam_batch)

theorem _root_.Fo.inv_Attention_Seam_objects (tl : HTailF2) (funs : Array HFun)  :
    Inv I (OnBytes.Attention.Seam.objects tl funs) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Attention_Seam_objects)

end OnBytes.Attention.Seam

namespace OnBytes.Attention
open Fo OnBytes.PscRun
open OnBytes.Model

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem _root_.Fo.inv_Attention_allJoined (j : Joins)  :
    Inv I (OnBytes.Attention.allJoined j) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_allJoined)

theorem _root_.Fo.inv_Attention_paddingLaid (S : Shape) (g : Forest.Heard)  :
    Inv I (OnBytes.Attention.paddingLaid S g) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Attention_paddingLaid)

theorem _root_.Fo.inv_Attention_noFreeSlot (nMsg : Nat)  :
    Inv I (OnBytes.Attention.noFreeSlot nMsg) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_noFreeSlot)

theorem _root_.Fo.inv_Attention_countsHeld (P : Plan) (tl : HTailF2)  :
    Inv I (OnBytes.Attention.countsHeld P tl) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_countsHeld)

theorem _root_.Fo.inv_Attention_hear (P : Plan)  :
    Inv I (OnBytes.Attention.hear P) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_hear)

theorem _root_.Fo.inv_Attention_claims (P : Plan) (h : Heard)  :
    Inv I (OnBytes.Attention.claims P h) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_claims)

end OnBytes.Attention
