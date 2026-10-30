-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheRooms.lean: the six numbers of the completeness error, each with a room, so that the target
is met by arithmetic. The error of the offline part has three numbers: public stops, private stops,
falls. The online part has three: public stops, private stops, falls. The link's is 0.

  theRoom                2⁻¹⁰⁰, the room of each of the six
  offlineBadRoom, offlineHidRoom, offlineFallRoom, onlineBadRoom, onlineHidRoom, onlineFallRoom
                         the six rooms, by name
  rooms_add              six numbers within their rooms add up to at most half of completenessErrorBound

Limits. Arithmetic alone. That any of the six numbers lies within its room is no part of this file.
-/
import Ladder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.TheRooms

/-- The room of each of the error's six numbers. -/
def theRoom : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 100

/-- The offline part's public stops. No such stop is known. -/
def offlineBadRoom : ℝ≥0∞ := theRoom

/-- The offline part's private stops. No such stop is known. -/
def offlineHidRoom : ℝ≥0∞ := theRoom

/-- The offline part's falls. No such fall is known. -/
def offlineFallRoom : ℝ≥0∞ := theRoom

/-- The online part's public stops. No such stop is known. -/
def onlineBadRoom : ℝ≥0∞ := theRoom

/-- The online part's private stops: the smallness test's window. -/
def onlineHidRoom : ℝ≥0∞ := theRoom

/-- The online part's falls and marks. -/
def onlineFallRoom : ℝ≥0∞ := theRoom

theorem half_le_one : (2 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 (by norm_num)

theorem eight_rooms : (8 : ℝ≥0∞) * theRoom = (2 : ℝ≥0∞)⁻¹ ^ 97 := by
  unfold theRoom
  have h₂ : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  calc (8 : ℝ≥0∞) * 2⁻¹ ^ 100 = ((2 : ℝ≥0∞) * 2⁻¹) ^ 3 * 2⁻¹ ^ 97 := by
        rw [mul_pow, show (100 : ℕ) = 3 + 97 from rfl, pow_add]
        norm_num
        ring
    _ = 2⁻¹ ^ 97 := by rw [h₂, one_pow, one_mul]

/-- **Six numbers within their rooms add up to at most half of completenessErrorBound.** The shape is the one in which
the completeness error adds them, with the link's 0 between the two parts. -/
theorem rooms_add {kB kH kF zB z pF : ℝ≥0∞} (h₁ : kB ≤ offlineBadRoom)
    (h₂ : kH ≤ offlineHidRoom) (h₃ : kF ≤ offlineFallRoom) (h₄ : zB ≤ onlineBadRoom)
    (h₅ : z ≤ onlineHidRoom) (h₆ : pF ≤ onlineFallRoom) :
    (kB + kH + kF) + 0 + (zB + z + pF) ≤ VerifierAndGoals.completenessErrorBound / 2 := by
  have e : VerifierAndGoals.completenessErrorBound / 2 = (2 : ℝ≥0∞)⁻¹ ^ 41 := by
    unfold VerifierAndGoals.completenessErrorBound
    rw [div_eq_mul_inv]
    exact (pow_succ _ 40).symm
  have l : (2 : ℝ≥0∞)⁻¹ ^ 97 ≤ 2⁻¹ ^ 41 :=
    pow_le_pow_right_of_le_one' half_le_one (by norm_num)
  rw [e]
  calc (kB + kH + kF) + 0 + (zB + z + pF)
      ≤ (theRoom + theRoom + theRoom) + 0 + (theRoom + theRoom + theRoom) :=
        add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) le_rfl)
          (add_le_add (add_le_add h₄ h₅) h₆)
    _ ≤ (8 : ℝ≥0∞) * theRoom := by
        have : (theRoom + theRoom + theRoom) + 0 + (theRoom + theRoom + theRoom) =
            (6 : ℝ≥0∞) * theRoom := by ring
        rw [this]
        gcongr
        norm_num
    _ = 2⁻¹ ^ 97 := eight_rooms
    _ ≤ 2⁻¹ ^ 41 := l

end AtPublicFiles.TheRooms

#print axioms AtPublicFiles.TheRooms.rooms_add
