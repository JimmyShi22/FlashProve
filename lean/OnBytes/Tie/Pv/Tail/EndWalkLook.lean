-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndWalkLook.lean: the routines of the masked sumcheck and of the lookup
(OnBytes/Model/Psc.lean, OnBytes/Model/Look.lean) keep whatever the basic steps keep.

Theorems with their proofs, one for each routine, each by a walk through the routine's text (`walk`,
OnBytes/Tie/Pv/Tail/EndWalk.lean). R: any relation with `Prim R`. «x keeps R»: wherever the routine
x returns, R holds from the state before to the state after (`Pres R x`, `PresL R x`).

Main names: `pres_` and the routine's name.

Limits: those of OnBytes/Tie/Pv/Tail/EndWalk.lean.


-/
import OnBytes.Model.Look
import OnBytes.Tie.Pv.Tail.EndWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

variable {R : Fork → Fork → Prop}

open OnBytes.Model in
/-- `pscBeginAt` keeps R. -/
instance pres_Model_pscBeginAt [Prim R] (target : E) :
    Pres R (OnBytes.Model.pscBeginAt target) := by
  unfold OnBytes.Model.pscBeginAt
  walk

open OnBytes.Model in
/-- `pscBegin` keeps R. -/
instance pres_Model_pscBegin [Prim R] (C : Aff) :
    Pres R (OnBytes.Model.pscBegin C) := by
  unfold OnBytes.Model.pscBegin
  walk

open OnBytes.Model in
/-- `pscRound` keeps R. -/
instance pres_Model_pscRound [Prim R] (p : Psc) (w : OnBytes.Psc.Weight) (draw : Blk E) :
    Pres R (OnBytes.Model.pscRound p w draw) := by
  unfold OnBytes.Model.pscRound
  walk

open OnBytes.Model in
/-- `roundIn` keeps R. -/
instance pres_Model_roundIn [Prim R] (form : RoundForm) (p : Psc) (z : E) (degree : Nat) :
    Pres R (OnBytes.Model.roundIn form p z degree) := by
  unfold OnBytes.Model.roundIn
  walk

open OnBytes.Model in
/-- `pscEnds` keeps R. -/
instance pres_Model_pscEnds [Prim R] (p : Psc) (degreeInY n : Nat) :
    Pres R (OnBytes.Model.pscEnds p degreeInY n) := by
  unfold OnBytes.Model.pscEnds
  walk

open OnBytes.Model in
/-- `pscRow` keeps R. -/
instance pres_Model_pscRow [Prim R] (p : Psc) (S0 : E) (kept : Aff) :
    Pres R (OnBytes.Model.pscRow p S0 kept) := by
  unfold OnBytes.Model.pscRow
  walk

/-- `levelRounds` keeps R. -/
instance pres_Model_levelRounds [Prim R] (mu : Nat) (rho : Array E) :
    ∀ (l : List Nat) (r : Array E) (p : Psc), Pres R (OnBytes.Model.levelRounds mu rho l r p)
  | [], r, p => by
    unfold OnBytes.Model.levelRounds
    walk
  | t :: l, r, p => by
    have := pres_Model_levelRounds mu rho l
    unfold OnBytes.Model.levelRounds
    walk

open OnBytes.Model in
/-- `levelIn` keeps R. -/
instance pres_Model_levelIn [Prim R] (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Pres R (OnBytes.Model.levelIn mu rho C order) := by
  unfold OnBytes.Model.levelIn
  walk

open OnBytes.Model in
/-- `layerObject` keeps R. -/
instance pres_Model_layerObject [Prim R] (o : Level) :
    Pres R (OnBytes.Model.layerObject o) := by
  unfold OnBytes.Model.layerObject
  walk

open OnBytes.Model in
/-- `uEnt` keeps R. -/
instance pres_Model_uEnt [Prim R] (t x : Nat) :
    Pres R (OnBytes.Model.uEnt t x) := by
  unfold OnBytes.Model.uEnt
  walk

open OnBytes.Model in
/-- `roundsIn` keeps R. -/
instance pres_Model_roundsIn [Prim R] (form : RoundForm) (p : Psc) (zs : List (E × Nat)) :
    Pres R (OnBytes.Model.roundsIn form p zs) := by
  unfold OnBytes.Model.roundsIn
  walk

open OnBytes.Model in
/-- `stackRounds` keeps R. -/
instance pres_Model_stackRounds [Prim R] (st : Stack) :
    Pres R (OnBytes.Model.stackRounds st) := by
  unfold OnBytes.Model.stackRounds
  walk

open OnBytes.Model.Forest in
/-- `Forest.draws` keeps R. -/
instance pres_Model_Forest_draws [Prim R] (h : Shape) :
    Pres R (OnBytes.Model.Forest.draws h) := by
  unfold OnBytes.Model.Forest.draws
  walk

open OnBytes.Model.Forest in
/-- `Forest.tieStep` keeps R. -/
instance pres_Model_Forest_tieStep [Prim R] (a : E) (s : TieStep) (j : Nat) :
    Pres R (OnBytes.Model.Forest.tieStep a s j) := by
  unfold OnBytes.Model.Forest.tieStep
  walk

open OnBytes.Model.Forest in
/-- `Forest.tie` keeps R. -/
instance pres_Model_Forest_tie [Prim R] (a : E) :
    Pres R (OnBytes.Model.Forest.tie a) := by
  unfold OnBytes.Model.Forest.tie
  walk

open OnBytes.Model.Forest in
/-- `Forest.level` keeps R. -/
instance pres_Model_Forest_level [Prim R] (s : Descent) (mu : Nat) (order : List Nat) :
    Pres R (OnBytes.Model.Forest.level s mu order) := by
  unfold OnBytes.Model.Forest.level
  walk

open OnBytes.Model.Forest in
/-- `Forest.pad` keeps R. -/
instance pres_Model_Forest_pad [Prim R] (calls : Array Call) (pub : Array Nat) (lid : Nat) :
    Pres R (OnBytes.Model.Forest.pad calls pub lid) := by
  unfold OnBytes.Model.Forest.pad
  walk

open OnBytes.Model.Forest in
/-- `Forest.objects` keeps R. -/
instance pres_Model_Forest_objects [Prim R] (g : Heard) :
    Pres R (OnBytes.Model.Forest.objects g) := by
  unfold OnBytes.Model.Forest.objects
  walk

open OnBytes.Model.Forest in
/-- `Forest.planesAdded` keeps R. -/
instance pres_Model_Forest_planesAdded [Prim R] (g : Heard) :
    Pres R (OnBytes.Model.Forest.planesAdded g) := by
  unfold OnBytes.Model.Forest.planesAdded
  walk

open OnBytes.Model.Forest in
/-- `Forest.joinAdded` keeps R. -/
instance pres_Model_Forest_joinAdded [Prim R] (g : Heard) :
    Pres R (OnBytes.Model.Forest.joinAdded g) := by
  unfold OnBytes.Model.Forest.joinAdded
  walk

open OnBytes.Model.Forest in
/-- `Forest.paddingLaid` keeps R. -/
instance pres_Model_Forest_paddingLaid [Prim R] (g : Heard) (laid : Array Nat) :
    Pres R (OnBytes.Model.Forest.paddingLaid g laid) := by
  unfold OnBytes.Model.Forest.paddingLaid
  walk

open OnBytes.Model.Forest in
/-- `Forest.join` keeps R. -/
instance pres_Model_Forest_join [Prim R] (g : Heard) (KF : Array Aff) :
    Pres R (OnBytes.Model.Forest.join g KF) := by
  unfold OnBytes.Model.Forest.join
  walk

open OnBytes.Model.Forest in
/-- `Forest.planesAt` keeps R. -/
instance pres_Model_Forest_planesAt [Prim R] (g : Heard) (lm e : Nat) (bit : Nat → Nat → SubM Aff)
    [∀ x0 x1, Pres R (bit x0 x1)] :
    Pres R (OnBytes.Model.Forest.planesAt g lm e bit) := by
  unfold OnBytes.Model.Forest.planesAt
  walk

open OnBytes.Model.Forest in
/-- `Forest.planeClaims` keeps R. -/
instance pres_Model_Forest_planeClaims [Prim R] (g : Heard) (lm : Nat) (bit : Nat → Nat → SubM Aff)
    (pin : Nat → SubM Aff) [∀ x0 x1, Pres R (bit x0 x1)] [∀ x0, Pres R (pin x0)] :
    Pres R (OnBytes.Model.Forest.planeClaims g lm bit pin) := by
  unfold OnBytes.Model.Forest.planeClaims
  walk

open OnBytes.Model.Forest in
/-- `Forest.planeLins` keeps R. -/
instance pres_Model_Forest_planeLins [Prim R] (g : Heard) (lm : Nat) (bit : Nat → Nat → SubM Aff)
    (pin : Nat → SubM Aff) [∀ x0 x1, Pres R (bit x0 x1)] [∀ x0, Pres R (pin x0)] :
    Pres R (OnBytes.Model.Forest.planeLins g lm bit pin) := by
  unfold OnBytes.Model.Forest.planeLins
  walk

end OnBytes.Tie.Pv.Tail.Walk

#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_pscRow
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_levelIn
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_Forest_pad
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_Model_Forest_planeLins
