-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedAtt.lean.
The attention sub-proof's and the lookup's routines of the second pass are Fo.Fixed.

States Fo.Fixed of: Attention.claim3, claim4, claim5, claim6, claim7, claim8, allJoined,
paddingLaid; Forest.objects, Forest.join, Forest.planeClaims and Forest.planeLins (for callers'
routines bit and pin that are Fixed); Attention.u3at. Each by the tactic fixed. What Fo.Fixed says
and what it leaves open stands in the head of OnBytes/Tie/Pv/Lookup/Ends/FoFixed.lean: value and
list are chosen behind the routine's arguments (the record of what was heard, the joins).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixed
import OnBytes.Model.Attention

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

theorem fixed_u3at (h : Attention.Heard) (t i : ℕ) : Fixed (u3at h t i) := by fixed
theorem fixed_claim3 (h : Attention.Heard) (j : Joins) : Fixed (claim3 h j) := by fixed
theorem fixed_claim4 (h : Attention.Heard) (j : Joins) : Fixed (claim4 h j) := by fixed
theorem fixed_claim5 (h : Attention.Heard) (j : Joins) : Fixed (claim5 h j) := by fixed
theorem fixed_claim6 (h : Attention.Heard) : Fixed (claim6 h) := by fixed
theorem fixed_claim7 (h : Attention.Heard) : Fixed (claim7 h) := by fixed
theorem fixed_claim8 (h : Attention.Heard) : Fixed (claim8 h) := by fixed
theorem fixed_allJoined (j : Joins) : Fixed (allJoined j) := by fixed
theorem fixed_paddingLaidA (S : Shape) (g : Forest.Heard) : Fixed (Attention.paddingLaid S g) := by
  fixed
theorem fixed_objects (g : Forest.Heard) : Fixed (Forest.objects g) := by fixed
theorem fixed_join (g : Forest.Heard) (KF : Array Aff) : Fixed (Forest.join g KF) := by fixed
theorem fixed_planeClaims (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Fixed (bit e col)) (hp : ∀ col, Fixed (pin col)) :
    Fixed (Forest.planeClaims g lm bit pin) := by fixed
theorem fixed_planeLins (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (hb : ∀ e col, Fixed (bit e col)) (hp : ∀ col, Fixed (pin col)) :
    Fixed (Forest.planeLins g lm bit pin) := by fixed

end Fo
