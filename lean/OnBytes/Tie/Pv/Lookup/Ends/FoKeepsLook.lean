-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLook.lean.
The lookup's own routines keep what lies under the filled slots.

`Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean) of levelRounds and levelIn (the product tree of
OnBytes/Model/Psc.lean) and of these routines of OnBytes/Model/Look.lean: level, pad, objects,
planesAdded, joinAdded, paddingLaid, join; of planeClaims and planeLins under the premise that the
callers' routines bit and pin have `Keeps`.
No statement of their own have layerObject (Psc.lean) and uEnt, roundsIn, stackRounds, draws,
tieStep, tie and planesAt (Look.lean): the tactic `keeps` opens them where a routine calls them.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsSteps

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem Keeps.levelRounds (mu : ℕ) (rho : Array E) :
    ∀ (order : List ℕ) (r : Array E) (p : Psc), Keeps (levelRounds mu rho order r p)
  | [], r, p => by
    rw [Model.levelRounds]
    exact Keeps.pure _
  | v :: order, r, p => by
    rw [Model.levelRounds]
    refine (Keeps.must _).bind fun _ => (Keeps.roundIn _ _ _ _).bind fun x => ?_
    exact Keeps.levelRounds mu rho order _ _

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible exact Keeps.levelRounds _ _ _ _ _)
macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible exact Keeps.roundIn _ _ _ _)
macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible exact Keeps.pscBegin _)
macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible exact Keeps.pscEnds _ _ _)
macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible exact Keeps.pscRow _ _ _)
macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible exact Keeps.claimsIn _)

theorem Keeps.levelIn (mu : ℕ) (rho : Array E) (C : Aff) (order : List ℕ) :
    Keeps (levelIn mu rho C order) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible exact Keeps.levelIn _ _ _ _)

theorem Keeps.level (s : Forest.Descent) (mu : ℕ) (order : List ℕ) :
    Keeps (Forest.level s mu order) := by keeps

theorem Keeps.pad (calls : Array Call) (pub : Array ℕ) (lid : ℕ) :
    Keeps (Forest.pad calls pub lid) := by keeps

theorem Keeps.objects (g : Forest.Heard) : Keeps (Forest.objects g) := by keeps
theorem Keeps.planesAdded (g : Forest.Heard) : Keeps (Forest.planesAdded g) := by keeps
theorem Keeps.joinAdded (g : Forest.Heard) : Keeps (Forest.joinAdded g) := by keeps
theorem Keeps.paddingLaid (g : Forest.Heard) (l : Array ℕ) : Keeps (Forest.paddingLaid g l) := by
  keeps
theorem Keeps.join (g : Forest.Heard) (KF : Array Aff) : Keeps (Forest.join g KF) := by keeps

theorem Keeps.planeClaims (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Keeps (bit e col)) (hp : ∀ col, Keeps (pin col)) :
    Keeps (Forest.planeClaims g lm bit pin) := by keeps

theorem Keeps.planeLins (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Keeps (bit e col)) (hp : ∀ col, Keeps (pin col)) :
    Keeps (Forest.planeLins g lm bit pin) := by
  unfold Forest.planeLins
  exact (Keeps.planeClaims g lm bit pin hb hp).bind fun _ =>
    (Keeps.arrayForM Keeps.lin _).bind fun _ => Keeps.planesAdded g

end Fo
