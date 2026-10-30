-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvLook.lean.
The lookup's own routines keep every property of the state that has `Prim`.

`Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) of each routine of OnBytes/Model/Psc.lean's product
tree and of
OnBytes/Model/Look.lean: levelRounds, levelIn, level, pad, objects, planesAdded, joinAdded,
paddingLaid, join; planeClaims and planeLins for callers' routines bit and pin that keep it.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvSteps

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem Inv.levelRounds (mu : ℕ) (rho : Array E) :
    ∀ (order : List ℕ) (r : Array E) (p : Psc), Inv I (levelRounds mu rho order r p)
  | [], r, p => by
    rw [Model.levelRounds]
    exact Inv.pure _
  | v :: order, r, p => by
    rw [Model.levelRounds]
    refine (Inv.must _).bind fun _ => (Inv.roundIn _ _ _ _).bind fun x => ?_
    exact Inv.levelRounds mu rho order _ _

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible exact Inv.levelRounds _ _ _ _ _)
macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible exact Inv.roundIn _ _ _ _)
macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible exact Inv.pscBegin _)
macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible exact Inv.pscEnds _ _ _)
macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible exact Inv.pscRow _ _ _)
macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible exact Inv.claimsIn _)

theorem Inv.levelIn (mu : ℕ) (rho : Array E) (C : Aff) (order : List ℕ) :
    Inv I (levelIn mu rho C order) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible exact Inv.levelIn _ _ _ _)

theorem Inv.level (s : Forest.Descent) (mu : ℕ) (order : List ℕ) :
    Inv I (Forest.level s mu order) := by inv

theorem Inv.pad (calls : Array Call) (pub : Array ℕ) (lid : ℕ) :
    Inv I (Forest.pad calls pub lid) := by inv

theorem Inv.objects (g : Forest.Heard) : Inv I (Forest.objects g) := by inv
theorem Inv.planesAdded (g : Forest.Heard) : Inv I (Forest.planesAdded g) := by inv
theorem Inv.joinAdded (g : Forest.Heard) : Inv I (Forest.joinAdded g) := by inv
theorem Inv.paddingLaid (g : Forest.Heard) (l : Array ℕ) : Inv I (Forest.paddingLaid g l) := by
  inv
theorem Inv.join (g : Forest.Heard) (KF : Array Aff) : Inv I (Forest.join g KF) := by inv

theorem Inv.planeClaims (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Inv I (bit e col)) (hp : ∀ col, Inv I (pin col)) :
    Inv I (Forest.planeClaims g lm bit pin) := by inv

theorem Inv.planeLins (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Inv I (bit e col)) (hp : ∀ col, Inv I (pin col)) :
    Inv I (Forest.planeLins g lm bit pin) := by
  unfold Forest.planeLins
  exact (Inv.planeClaims g lm bit pin hb hp).bind fun _ =>
    (Inv.arrayForM Inv.lin _).bind fun _ => Inv.planesAdded g

end Fo
