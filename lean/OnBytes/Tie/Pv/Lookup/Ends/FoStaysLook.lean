-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysLook.lean.
Eleven routines stay on the view: levelRounds and levelIn (the product tree of
OnBytes/Model/Psc.lean), and of OnBytes/Model/Look.lean: level, pad, objects, planesAdded,
joinAdded, paddingLaid, join, planeClaims, planeLins.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: from every state, a run on a view that returns is still on the view (`Dry`,
OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean: the mark of the dry run, false before, is false behind).
Nothing is said of a run that refuses, or of what a run reads. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Nine are proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; levelRounds, which is
defined by recursion, by induction; planeLins by the rules for bind, by hand. planeClaims and
planeLins stand under the same of the callers' routines bit and pin.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysSteps

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem DryS.levelRounds (mu : ℕ) (rho : Array E) :
    ∀ (order : List ℕ) (r : Array E) (p : Psc), DryS (levelRounds mu rho order r p)
  | [], r, p => by
    rw [Model.levelRounds]
    exact DryS.pure _
  | v :: order, r, p => by
    rw [Model.levelRounds]
    refine (DryS.must _).bind fun _ => (DryS.roundIn _ _ _ _).bind fun x => ?_
    exact DryS.levelRounds mu rho order _ _

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact DryS.levelRounds _ _ _ _ _)
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact DryS.roundIn _ _ _ _)
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact DryS.pscBegin _)
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact DryS.pscEnds _ _ _)
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact DryS.pscRow _ _ _)
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact DryS.claimsIn _)

theorem DryS.levelIn (mu : ℕ) (rho : Array E) (C : Aff) (order : List ℕ) :
    DryS (levelIn mu rho C order) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact DryS.levelIn _ _ _ _)

theorem DryS.level (s : Forest.Descent) (mu : ℕ) (order : List ℕ) :
    DryS (Forest.level s mu order) := by stays

theorem DryS.pad (calls : Array Call) (pub : Array ℕ) (lid : ℕ) :
    DryS (Forest.pad calls pub lid) := by stays

theorem DryS.objects (g : Forest.Heard) : DryS (Forest.objects g) := by stays
theorem DryS.planesAdded (g : Forest.Heard) : DryS (Forest.planesAdded g) := by stays
theorem DryS.joinAdded (g : Forest.Heard) : DryS (Forest.joinAdded g) := by stays
theorem DryS.paddingLaid (g : Forest.Heard) (l : Array ℕ) : DryS (Forest.paddingLaid g l) := by
  stays
theorem DryS.join (g : Forest.Heard) (KF : Array Aff) : DryS (Forest.join g KF) := by stays

theorem DryS.planeClaims (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, DryS (bit e col)) (hp : ∀ col, DryS (pin col)) :
    DryS (Forest.planeClaims g lm bit pin) := by stays

theorem DryS.planeLins (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, DryS (bit e col)) (hp : ∀ col, DryS (pin col)) :
    DryS (Forest.planeLins g lm bit pin) := by
  unfold Forest.planeLins
  exact (DryS.planeClaims g lm bit pin hb hp).bind fun _ =>
    (DryS.arrayForM DryS.lin _).bind fun _ => DryS.planesAdded g

end Fo
