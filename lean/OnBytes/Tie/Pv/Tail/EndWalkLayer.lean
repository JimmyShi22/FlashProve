-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndWalkLayer.lean: the routines of a layer group's sub-proof
(OnBytes/Model/Layer.lean) keep whatever the basic steps keep.

Theorems with their proofs, one for each routine, each by a walk through the routine's text (`walk`,
OnBytes/Tie/Pv/Tail/EndWalk.lean). R: any relation with `Prim R`. «x keeps R»: wherever the routine
x returns, R holds from the state before to the state after (`Pres R x`, `PresL R x`).

Main names: `pres_` and the routine's name.

Limits: those of OnBytes/Tie/Pv/Tail/EndWalk.lean.


-/
import OnBytes.Model.Layer
import OnBytes.Tie.Pv.Tail.EndWalkHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {R : Fork → Fork → Prop}

open OnBytes.Model.Layer in
/-- `Layer.form` keeps R. -/
instance pres_Model_Layer_form [Prim R] {α : Type} (x : Option α) :
    Pres R (OnBytes.Model.Layer.form x) := by
  unfold OnBytes.Model.Layer.form
  walk2

open OnBytes.Model.Layer in
/-- `Layer.note` keeps R. -/
instance pres_Model_Layer_note [Prim R] (what : String) (x : E) :
    Pres R (OnBytes.Model.Layer.note what x) := by
  unfold OnBytes.Model.Layer.note
  walk2

open OnBytes.Model.Layer in
/-- `Layer.noteClaims` keeps R. -/
instance pres_Model_Layer_noteClaims [Prim R] (what : String) :
    Pres R (OnBytes.Model.Layer.noteClaims what) := by
  unfold OnBytes.Model.Layer.noteClaims
  walk2

open OnBytes.Model.Layer in
/-- `Layer.shownRun` keeps R. -/
instance pres_Model_Layer_shownRun [Prim R] (first n : Nat) :
    Pres R (OnBytes.Model.Layer.shownRun first n) := by
  unfold OnBytes.Model.Layer.shownRun
  walk2

open OnBytes.Model.Layer in
/-- `Layer.hearLook` keeps R. -/
instance pres_Model_Layer_hearLook [Prim R] (y : Lay) (g : Nat) :
    Pres R (OnBytes.Model.Layer.hearLook y g) := by
  unfold OnBytes.Model.Layer.hearLook
  walk2

open OnBytes.Model.Layer in
/-- `Layer.hearNorms` keeps R. -/
instance pres_Model_Layer_hearNorms [Prim R] (P : Pub) (g : Nat) (fo : Forest.Heard) :
    Pres R (OnBytes.Model.Layer.hearNorms P g fo) := by
  unfold OnBytes.Model.Layer.hearNorms
  walk2

open OnBytes.Model.Layer in
/-- `Layer.hearTerms` keeps R. -/
instance pres_Model_Layer_hearTerms [Prim R] (P : Pub) (H : Heard) :
    Pres R (OnBytes.Model.Layer.hearTerms P H) := by
  unfold OnBytes.Model.Layer.hearTerms
  walk2

open OnBytes.Model.Layer in
/-- `Layer.joinStart` keeps R. -/
instance pres_Model_Layer_joinStart [Prim R] (v : Env) (H : Heard) (om : Array E) :
    Pres R (OnBytes.Model.Layer.joinStart v H om) := by
  unfold OnBytes.Model.Layer.joinStart
  walk2

open OnBytes.Model.Layer in
/-- `Layer.hearStack` keeps R. -/
instance pres_Model_Layer_hearStack [Prim R] (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    Pres R (OnBytes.Model.Layer.hearStack P v H lamS NCLp) := by
  unfold OnBytes.Model.Layer.hearStack
  walk2

open OnBytes.Model.Layer in
/-- `Layer.hearGated` keeps R. -/
instance pres_Model_Layer_hearGated [Prim R] (P : Pub) (H : Heard) (K : HeardStack) :
    Pres R (OnBytes.Model.Layer.hearGated P H K) := by
  unfold OnBytes.Model.Layer.hearGated
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimsNorms` keeps R. -/
instance pres_Model_Layer_claimsNorms [Prim R] (P : Pub) (v : Env) (H : Heard) :
    Pres R (OnBytes.Model.Layer.claimsNorms P v H) := by
  unfold OnBytes.Model.Layer.claimsNorms
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimRowBatch` keeps R. -/
instance pres_Model_Layer_claimRowBatch [Prim R] (y : Lay) (H : Heard) :
    Pres R (OnBytes.Model.Layer.claimRowBatch y H) := by
  unfold OnBytes.Model.Layer.claimRowBatch
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimsLedger5` keeps R. -/
instance pres_Model_Layer_claimsLedger5 [Prim R] (v : Env) (H : Heard) :
    Pres R (OnBytes.Model.Layer.claimsLedger5 v H) := by
  unfold OnBytes.Model.Layer.claimsLedger5
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimsLedger4` keeps R. -/
instance pres_Model_Layer_claimsLedger4 [Prim R] (v : Env) (H : Heard) :
    Pres R (OnBytes.Model.Layer.claimsLedger4 v H) := by
  unfold OnBytes.Model.Layer.claimsLedger4
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimsTerms` keeps R. -/
instance pres_Model_Layer_claimsTerms [Prim R] (v : Env) (H : Heard) :
    Pres R (OnBytes.Model.Layer.claimsTerms v H) := by
  unfold OnBytes.Model.Layer.claimsTerms
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimsEnds` keeps R. -/
instance pres_Model_Layer_claimsEnds [Prim R] (v : Env) (o : Level) (e : Array E)
    (t rows blocks stride : Nat) (lamOf : Nat → Nat) (first : Nat) :
    Pres R (OnBytes.Model.Layer.claimsEnds v o e t rows blocks stride lamOf first) := by
  unfold OnBytes.Model.Layer.claimsEnds
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimsGated` keeps R. -/
instance pres_Model_Layer_claimsGated [Prim R] (P : Pub) (v : Env) (hd : Level)
    (hd2 : Option Level) :
    Pres R (OnBytes.Model.Layer.claimsGated P v hd hd2) := by
  unfold OnBytes.Model.Layer.claimsGated
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimsOneHot` keeps R. -/
instance pres_Model_Layer_claimsOneHot [Prim R] (v : Env) :
    Pres R (OnBytes.Model.Layer.claimsOneHot v) := by
  unfold OnBytes.Model.Layer.claimsOneHot
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimsPlanes` keeps R. -/
instance pres_Model_Layer_claimsPlanes [Prim R] (v : Env) (fo : Forest.Heard) :
    Pres R (OnBytes.Model.Layer.claimsPlanes v fo) := by
  unfold OnBytes.Model.Layer.claimsPlanes
  walk2

open OnBytes.Model.Layer in
/-- `Layer.claimEmbedding` keeps R. -/
instance pres_Model_Layer_claimEmbedding [Prim R] (v : Env) (H : Heard) (sVE : Nat) :
    Pres R (OnBytes.Model.Layer.claimEmbedding v H sVE) := by
  unfold OnBytes.Model.Layer.claimEmbedding
  walk2

open OnBytes.Model.Layer in
/-- `Layer.freeSlotTest` keeps R. -/
instance pres_Model_Layer_freeSlotTest [Prim R] (g used sFv : Nat) :
    Pres R (OnBytes.Model.Layer.freeSlotTest g used sFv) := by
  unfold OnBytes.Model.Layer.freeSlotTest
  walk2

open OnBytes.Model.Layer in
/-- `Layer.hearOwn` keeps R. -/
instance pres_Model_Layer_hearOwn [Prim R] (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) :
    Pres R (OnBytes.Model.Layer.hearOwn P hp g fo) := by
  unfold OnBytes.Model.Layer.hearOwn
  walk2

end OnBytes.Tie.Pv.Tail.Walk

#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_Layer_hearOwn
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_Layer_claimsGated
