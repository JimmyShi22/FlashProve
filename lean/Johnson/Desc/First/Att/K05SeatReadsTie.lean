-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05SeatReadsTie.lean: kind K5: THE CLAUSE reads OF FrontAll
(Johnson/Desc/First/Att/K05BehindWorth.lean) FROM A YES OF THE TABLE's ITEM look m's BOOL AT AN
ATTENTION SEGMENT (lookAttB, Johnson/Desc/First/Att/Door/PubK5.lean) AND "what the lookup has heard
is gL" (S.lookHeard?: the reader that the lookup's promise pins).

Main names:
  `seatReads_of_same`: sameHeardB g gL = true gives SeatReadsSame g gL
    (Johnson/Desc/First/Att/K05SameRead.lean): four of sameHeard_gives' seventeen equations
    (Johnson/Desc/First/Att/Door/LookGives.lean); the shapes are one by sameHeard_shape_eq
    (Johnson/Desc/First/Att/Door/ShapeSame.lean): CALLED.
  `seatReads_of_look`: lookAttB s = true and s.lookHeard? = some gL give: wherever s.here = .att a₀:
    ∃ g, a₀.g = some g ∧ SeatReadsSame g gL.
  `plain_of_look`: and gL's closing form names no entry (FrontAll's clause plain).
Limits. lookAttB has run at no record.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.ShapeSame
import Johnson.Desc.First.Att.K05SameRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open H2K5.Door (sameHeardB lookAttB lookAttUpTo sameHeard_gives sameHeard_shape_eq lookAtt_opens)

theorem seatReads_of_same {g gL : Forest.Heard} (e : sameHeardB g gL = true) :
    SeatReadsSame g gL := by
  obtain ⟨_, _, _, _, _, zx, _, _, zb0, zb1, _, zk, _⟩ := sameHeard_gives e
  exact ⟨zk, zx, zb0, zb1, sameHeard_shape_eq e⟩

theorem seatReads_of_look {s : First.S} {gL : Forest.Heard} (e : lookAttB s = true)
    (hl : s.lookHeard? = some gL) :
    ∀ a₀, s.here = .att a₀ → ∃ g, a₀.g = some g ∧ SeatReadsSame g gL := by
  obtain ⟨a, g, gL', ha, hg, hh, hs⟩ := lookAtt_opens e
  intro a₀ h0
  rw [ha] at h0
  cases h0
  have : gL' = gL := by
    unfold First.S.lookHeard? at hl
    rw [ha] at hl
    exact Option.some.inj (hh.symm.trans hl)
  subst this
  exact ⟨g, hg, seatReads_of_same hs⟩

/-- The lookup's closing form names no entry. -/
theorem plain_of_look {s : First.S} {gL : Forest.Heard} (e : lookAttB s = true)
    (hl : s.lookHeard? = some gL) : gL.cEnd.ents = #[] := by
  unfold lookAttB lookAttUpTo at e
  unfold First.S.lookHeard? at hl
  split at e
  · rename_i a ha
    rw [ha] at hl
    split at e
    · rename_i g gL' e1 e2
      obtain rfl : gL' = gL := Option.some.inj (e2.symm.trans hl)
      simp only [Bool.and_eq_true] at e
      exact Array.isEmpty_iff.1 e.1.2
    · cases e
  · cases e

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seatReads_of_same
#print axioms VerifiableInference.Desc.First.Att.P.seatReads_of_look
#print axioms VerifiableInference.Desc.First.Att.P.plain_of_look
