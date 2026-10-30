-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvLayer.lean.
The routines of OnBytes/Model/Layer.lean keep every property of the state that has `Prim`.

One statement a routine, but for those named under "Left out": `Inv I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a
routine of a link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Left out: Layer.runForkHidG2 (no statement: it sets the slots up anew, or calls a routine that
does).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvTail
import OnBytes.Model.Layer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model OnBytes.Model.Layer

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem inv_Model_Layer_form {α : Type} (x : Option α)  :
    Inv I (OnBytes.Model.Layer.form x) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_form)

theorem inv_Model_Layer_note (what : String) (x : E)  :
    Inv I (OnBytes.Model.Layer.note what x) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_note)

theorem inv_Model_Layer_noteClaims (what : String)  :
    Inv I (OnBytes.Model.Layer.noteClaims what) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_noteClaims)

theorem inv_Model_Layer_shownRun (first n : Nat)  :
    Inv I (OnBytes.Model.Layer.shownRun first n) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_shownRun)

theorem inv_Model_Layer_hearLook (y : Lay) (g : Nat)  :
    Inv I (OnBytes.Model.Layer.hearLook y g) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_hearLook)

theorem inv_Model_Layer_hearNorms (P : Pub) (g : Nat) (fo : Forest.Heard)  :
    Inv I (OnBytes.Model.Layer.hearNorms P g fo) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_hearNorms)

theorem inv_Model_Layer_hearTerms (P : Pub) (H : Heard)  :
    Inv I (OnBytes.Model.Layer.hearTerms P H) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_hearTerms)

theorem inv_Model_Layer_joinStart (v : Env) (H : Heard) (om : Array E)  :
    Inv I (OnBytes.Model.Layer.joinStart v H om) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_joinStart)

theorem inv_Model_Layer_hearStack (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat)  :
    Inv I (OnBytes.Model.Layer.hearStack P v H lamS NCLp) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_hearStack)

theorem inv_Model_Layer_hearGated (P : Pub) (H : Heard) (K : HeardStack)  :
    Inv I (OnBytes.Model.Layer.hearGated P H K) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_hearGated)

theorem inv_Model_Layer_claimsNorms (P : Pub) (v : Env) (H : Heard)  :
    Inv I (OnBytes.Model.Layer.claimsNorms P v H) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_claimsNorms)

theorem inv_Model_Layer_claimRowBatch (y : Lay) (H : Heard)  :
    Inv I (OnBytes.Model.Layer.claimRowBatch y H) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_Layer_claimRowBatch)

theorem inv_Model_Layer_claimsLedger5 (v : Env) (H : Heard)  :
    Inv I (OnBytes.Model.Layer.claimsLedger5 v H) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_Layer_claimsLedger5)

theorem inv_Model_Layer_claimsLedger4 (v : Env) (H : Heard)  :
    Inv I (OnBytes.Model.Layer.claimsLedger4 v H) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_Layer_claimsLedger4)

theorem inv_Model_Layer_claimsTerms (v : Env) (H : Heard)  :
    Inv I (OnBytes.Model.Layer.claimsTerms v H) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_claimsTerms)

theorem inv_Model_Layer_claimsEnds (v : Env) (o : Level) (e : Array E) (t rows blocks stride :
    Nat) (lamOf : Nat → Nat) (first : Nat)  :
    Inv I (OnBytes.Model.Layer.claimsEnds v o e t rows blocks stride lamOf first) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_claimsEnds)

theorem inv_Model_Layer_claimsGated (P : Pub) (v : Env) (hd : Level) (hd2 : Option Level)  :
    Inv I (OnBytes.Model.Layer.claimsGated P v hd hd2) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_claimsGated)

theorem inv_Model_Layer_claimsOneHot (v : Env)  :
    Inv I (OnBytes.Model.Layer.claimsOneHot v) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_Layer_claimsOneHot)

theorem inv_Model_Layer_claimsPlanes (v : Env) (fo : Forest.Heard)  :
    Inv I (OnBytes.Model.Layer.claimsPlanes v fo) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_Layer_claimsPlanes)

theorem inv_Model_Layer_claimEmbedding (v : Env) (H : Heard) (sVE : Nat)  :
    Inv I (OnBytes.Model.Layer.claimEmbedding v H sVE) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_Layer_claimEmbedding)

theorem inv_Model_Layer_freeSlotTest (g used sFv : Nat)  :
    Inv I (OnBytes.Model.Layer.freeSlotTest g used sFv) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_Layer_freeSlotTest)

theorem inv_Model_Layer_hearOwn (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard)  :
    Inv I (OnBytes.Model.Layer.hearOwn P hp g fo) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_Layer_hearOwn)

end Fo
