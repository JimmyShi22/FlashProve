-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLayer.lean.
Routines of OnBytes/Model/Layer.lean that keep what lies under the filled slots.

One statement for each routine but those that are left out (see below): `Keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean) or, for a routine of a link, `KeepsL`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine takes routines as arguments, the
statement has the premise that each of these has `Keeps`. Neither property says anything of a run in
which the routine refuses. Each statement is also given as a rule to the tactic `keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Left out: runForkHidG2, the sub-proof's whole check, which sets up the slots anew (Fork.slots) and
so does not keep what lay under them (by reading; no theorem).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsTail
import OnBytes.Model.Layer

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model OnBytes.Model.Layer

theorem keeps_Model_Layer_form {α : Type} (x : Option α)  :
    Keeps (OnBytes.Model.Layer.form x) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_form)

theorem keeps_Model_Layer_note (what : String) (x : E)  :
    Keeps (OnBytes.Model.Layer.note what x) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_note)

theorem keeps_Model_Layer_noteClaims (what : String)  :
    Keeps (OnBytes.Model.Layer.noteClaims what) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_noteClaims)

theorem keeps_Model_Layer_shownRun (first n : Nat)  :
    Keeps (OnBytes.Model.Layer.shownRun first n) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_shownRun)

theorem keeps_Model_Layer_hearLook (y : Lay) (g : Nat)  :
    Keeps (OnBytes.Model.Layer.hearLook y g) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_hearLook)

theorem keeps_Model_Layer_hearNorms (P : Pub) (g : Nat) (fo : Forest.Heard)  :
    Keeps (OnBytes.Model.Layer.hearNorms P g fo) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_hearNorms)

theorem keeps_Model_Layer_hearTerms (P : Pub) (H : Heard)  :
    Keeps (OnBytes.Model.Layer.hearTerms P H) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_hearTerms)

theorem keeps_Model_Layer_joinStart (v : Env) (H : Heard) (om : Array E)  :
    Keeps (OnBytes.Model.Layer.joinStart v H om) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_joinStart)

theorem keeps_Model_Layer_hearStack (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat)  :
    Keeps (OnBytes.Model.Layer.hearStack P v H lamS NCLp) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_hearStack)

theorem keeps_Model_Layer_hearGated (P : Pub) (H : Heard) (K : HeardStack)  :
    Keeps (OnBytes.Model.Layer.hearGated P H K) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_hearGated)

theorem keeps_Model_Layer_claimsNorms (P : Pub) (v : Env) (H : Heard)  :
    Keeps (OnBytes.Model.Layer.claimsNorms P v H) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_claimsNorms)

theorem keeps_Model_Layer_claimRowBatch (y : Lay) (H : Heard)  :
    Keeps (OnBytes.Model.Layer.claimRowBatch y H) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_Layer_claimRowBatch)

theorem keeps_Model_Layer_claimsLedger5 (v : Env) (H : Heard)  :
    Keeps (OnBytes.Model.Layer.claimsLedger5 v H) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_Layer_claimsLedger5)

theorem keeps_Model_Layer_claimsLedger4 (v : Env) (H : Heard)  :
    Keeps (OnBytes.Model.Layer.claimsLedger4 v H) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_Layer_claimsLedger4)

theorem keeps_Model_Layer_claimsTerms (v : Env) (H : Heard)  :
    Keeps (OnBytes.Model.Layer.claimsTerms v H) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_claimsTerms)

theorem keeps_Model_Layer_claimsEnds (v : Env) (o : Level) (e : Array E) (t rows blocks stride :
    Nat) (lamOf : Nat → Nat) (first : Nat)  :
    Keeps (OnBytes.Model.Layer.claimsEnds v o e t rows blocks stride lamOf first) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_claimsEnds)

theorem keeps_Model_Layer_claimsGated (P : Pub) (v : Env) (hd : Level) (hd2 : Option Level)  :
    Keeps (OnBytes.Model.Layer.claimsGated P v hd hd2) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_claimsGated)

theorem keeps_Model_Layer_claimsOneHot (v : Env)  :
    Keeps (OnBytes.Model.Layer.claimsOneHot v) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_Layer_claimsOneHot)

theorem keeps_Model_Layer_claimsPlanes (v : Env) (fo : Forest.Heard)  :
    Keeps (OnBytes.Model.Layer.claimsPlanes v fo) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_Layer_claimsPlanes)

theorem keeps_Model_Layer_claimEmbedding (v : Env) (H : Heard) (sVE : Nat)  :
    Keeps (OnBytes.Model.Layer.claimEmbedding v H sVE) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_Layer_claimEmbedding)

theorem keeps_Model_Layer_freeSlotTest (g used sFv : Nat)  :
    Keeps (OnBytes.Model.Layer.freeSlotTest g used sFv) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_Layer_freeSlotTest)

theorem keeps_Model_Layer_hearOwn (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard)  :
    Keeps (OnBytes.Model.Layer.hearOwn P hp g fo) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_Layer_hearOwn)

end Fo
