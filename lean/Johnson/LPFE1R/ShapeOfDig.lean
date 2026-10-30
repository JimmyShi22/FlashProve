-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/ShapeOfDig.lean: THE SHAPE THAT THE DIGITS' LOOKUP's
PARAMETERS FIX AT LINK m IS tlD.f9, WHERE digAt X m = some (xx, tlD): by the two definitions' texts
(Look/LookKind.lean: placeAt; Look/K3Asks.lean: digAt). One statement and its proof. WHAT IT IS FOR:
leftOn_digits_front | leftOn_digits_head (Link/Law/KxAtFront.lean)
end in "∃ P' hh, placeAt … m true = some P' ∧ P'.shape = some hh ∧ … K3LeftOn … hh …":
with this hh is tlD.f9: the premise L of three_of_leftOn | three_of_dig.
Limits. A fact on two definitions. No soundness statement.

-/
import Johnson.Desc.First.Look.K3Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (placeAt lookAt P)
open VerifiableInference.Desc.K3Asks (digAt)

/-- **The place's own shape is the one that digAt lays in the record.** -/
theorem shape_of_dig {X : Verify.Public} {m : Nat} {xx : First.Look.Place} {tlD : HTailF2}
    (hd : digAt X m = some (xx, tlD)) :
    ∀ P' hh, placeAt X m true = some P' → P'.shape = some hh → hh = tlD.f9 := by
  intro P' hh hP hs
  unfold digAt at hd
  obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 hd
  obtain ⟨tl, -, h3⟩ := Option.bind_eq_some_iff.1 h2
  obtain ⟨sh, hsh, h4⟩ := Option.map_eq_some_iff.1 h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
  unfold placeAt at hP
  rw [hy] at hP
  obtain rfl := Option.some.inj hP
  exact Option.some.inj (hs.symm.trans hsh)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shape_of_dig
