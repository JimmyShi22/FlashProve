-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysLayer.lean.
Twenty-two routines of OnBytes/Model/Layer.lean stay on the view: form, note, noteClaims, shownRun,
hearLook, hearNorms, hearTerms, joinStart, hearStack, hearGated, claimsNorms, claimRowBatch,
claimsLedger5, claimsLedger4, claimsTerms, claimsEnds, claimsGated, claimsOneHot, claimsPlanes,
claimEmbedding, freeSlotTest, hearOwn.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: from every state, a run on a view that returns is still on the view (`Dry`,
OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean: the mark of the dry run, false before, is false behind).
Nothing is said of a run that refuses, or of what a run reads. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysTail
import OnBytes.Model.Layer

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model OnBytes.Model.Layer

theorem stays_Model_Layer_form {α : Type} (x : Option α)  :
    DryS (OnBytes.Model.Layer.form x) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_form)

theorem stays_Model_Layer_note (what : String) (x : E)  :
    DryS (OnBytes.Model.Layer.note what x) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_note)

theorem stays_Model_Layer_noteClaims (what : String)  :
    DryS (OnBytes.Model.Layer.noteClaims what) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_noteClaims)

theorem stays_Model_Layer_shownRun (first n : Nat)  :
    DryS (OnBytes.Model.Layer.shownRun first n) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_shownRun)

theorem stays_Model_Layer_hearLook (y : Lay) (g : Nat)  :
    DryS (OnBytes.Model.Layer.hearLook y g) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_hearLook)

theorem stays_Model_Layer_hearNorms (P : Pub) (g : Nat) (fo : Forest.Heard)  :
    DryS (OnBytes.Model.Layer.hearNorms P g fo) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_hearNorms)

theorem stays_Model_Layer_hearTerms (P : Pub) (H : Heard)  :
    DryS (OnBytes.Model.Layer.hearTerms P H) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_hearTerms)

theorem stays_Model_Layer_joinStart (v : Env) (H : Heard) (om : Array E)  :
    DryS (OnBytes.Model.Layer.joinStart v H om) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_joinStart)

theorem stays_Model_Layer_hearStack (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat)  :
    DryS (OnBytes.Model.Layer.hearStack P v H lamS NCLp) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_hearStack)

theorem stays_Model_Layer_hearGated (P : Pub) (H : Heard) (K : HeardStack)  :
    DryS (OnBytes.Model.Layer.hearGated P H K) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_hearGated)

theorem stays_Model_Layer_claimsNorms (P : Pub) (v : Env) (H : Heard)  :
    DryS (OnBytes.Model.Layer.claimsNorms P v H) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_claimsNorms)

theorem stays_Model_Layer_claimRowBatch (y : Lay) (H : Heard)  :
    DryS (OnBytes.Model.Layer.claimRowBatch y H) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_Layer_claimRowBatch)

theorem stays_Model_Layer_claimsLedger5 (v : Env) (H : Heard)  :
    DryS (OnBytes.Model.Layer.claimsLedger5 v H) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_Layer_claimsLedger5)

theorem stays_Model_Layer_claimsLedger4 (v : Env) (H : Heard)  :
    DryS (OnBytes.Model.Layer.claimsLedger4 v H) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_Layer_claimsLedger4)

theorem stays_Model_Layer_claimsTerms (v : Env) (H : Heard)  :
    DryS (OnBytes.Model.Layer.claimsTerms v H) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_claimsTerms)

theorem stays_Model_Layer_claimsEnds (v : Env) (o : Level) (e : Array E) (t rows blocks stride :
    Nat) (lamOf : Nat → Nat) (first : Nat)  :
    DryS (OnBytes.Model.Layer.claimsEnds v o e t rows blocks stride lamOf first) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_claimsEnds)

theorem stays_Model_Layer_claimsGated (P : Pub) (v : Env) (hd : Level) (hd2 : Option Level)  :
    DryS (OnBytes.Model.Layer.claimsGated P v hd hd2) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_claimsGated)

theorem stays_Model_Layer_claimsOneHot (v : Env)  :
    DryS (OnBytes.Model.Layer.claimsOneHot v) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_Layer_claimsOneHot)

theorem stays_Model_Layer_claimsPlanes (v : Env) (fo : Forest.Heard)  :
    DryS (OnBytes.Model.Layer.claimsPlanes v fo) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_Layer_claimsPlanes)

theorem stays_Model_Layer_claimEmbedding (v : Env) (H : Heard) (sVE : Nat)  :
    DryS (OnBytes.Model.Layer.claimEmbedding v H sVE) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_Layer_claimEmbedding)

theorem stays_Model_Layer_freeSlotTest (g used sFv : Nat)  :
    DryS (OnBytes.Model.Layer.freeSlotTest g used sFv) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_Layer_freeSlotTest)

theorem stays_Model_Layer_hearOwn (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard)  :
    DryS (OnBytes.Model.Layer.hearOwn P hp g fo) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_Layer_hearOwn)

end Fo
