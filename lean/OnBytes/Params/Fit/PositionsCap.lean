-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/PositionsCap.lean: the number of positions that the derivation finds for a list
is at most 2 ^ 32.

"positions" (OnBytes/Params/Distance.lean) seeks the least number of positions at which a comparison
holds: "firstOk" doubles a bound from 1 on, and goes on only while the double is at most 2 ^ 32;
"leastOk" bisects between half the bound and the bound. "scopePositions" (OnBytes/Params/Group.lean)
is "positions" at a setting's numbers.

Main theorems, each without a premise on the comparison, the bounds or the setting.
 - firstOk_le: from a start of at most 2 ^ 32, what firstOk finds is at most 2 ^ 32.
 - leastOk_le: what leastOk returns is at most its upper end.
 - positions_le, scopePositions_le: at most 2 ^ 32.

Limits. Nothing on whether the number found is the least, or whether the comparison holds at it.
Where the search finds none, the number is 0; the bound says nothing on that. The program does not
import this file.


-/
import OnBytes.Params.Group

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Fit

/-- From a start of at most 2 ^ 32, what the doubling finds is at most 2 ^ 32. -/
theorem firstOk_le (ok : Nat → Bool) : ∀ (fuel hi r : Nat), hi ≤ 2 ^ 32 →
    firstOk ok fuel hi = some r → r ≤ 2 ^ 32 := by
  intro fuel
  induction fuel with
  | zero =>
    intro hi r _ h
    simp [firstOk] at h
  | succ n ih =>
    intro hi r hh h
    unfold firstOk at h
    split at h
    · cases h
      exact hh
    · split at h
      · cases h
      · rename_i _ h2
        exact ih (2 * hi) r (Nat.le_of_not_lt h2) h

/-- What the bisection returns is at most its upper end. -/
theorem leastOk_le (ok : Nat → Bool) : ∀ (fuel lo hi : Nat), leastOk ok fuel lo hi ≤ hi := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    simp [leastOk]
  | succ n ih =>
    intro lo hi
    unfold leastOk
    split
    · rename_i h1
      dsimp only
      split
      · exact Nat.le_trans (ih lo (lo + (hi - lo) / 2)) (by omega)
      · exact ih (lo + (hi - lo) / 2) hi
    · exact Nat.le_refl hi

/-- The number of positions is at most 2 ^ 32. -/
theorem positions_le (agree : Bound) (bits : Nat) (extra : Bound) (factor : Nat) :
    positions agree bits extra factor ≤ 2 ^ 32 := by
  unfold positions
  split
  · exact Nat.zero_le _
  · dsimp only
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.zero_le _
      · rename_i hi h
        exact Nat.le_trans (leastOk_le _ 40 (hi / 2) hi)
          (firstOk_le _ 40 1 hi (by omega) h)

/-- **The number of positions of a list in a scope is at most 2 ^ 32.** -/
theorem scopePositions_le (s : Setting) (c : Scope) (agree extra : Bound) :
    scopePositions s c agree extra ≤ 2 ^ 32 := by
  unfold scopePositions
  exact positions_le _ _ _ _

end OnBytes.Params.Fit

#print axioms OnBytes.Params.Fit.firstOk_le
#print axioms OnBytes.Params.Fit.leastOk_le
#print axioms OnBytes.Params.Fit.positions_le
#print axioms OnBytes.Params.Fit.scopePositions_le
