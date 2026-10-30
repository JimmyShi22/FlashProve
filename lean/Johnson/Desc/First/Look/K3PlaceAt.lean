-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PlaceAt.lean: the lookup's parameters at a link of a public record ARE the
parameters in the plan's own place: placeAt X i digits = some p just where lookAt X i digits gives a
place x and p = P.ofPlace (Params.settingOf X.P.frame) digits x. One statement, by unfolding.

Why. The end theorems at a public record (Johnson/Desc/First/Look/K3CallerAttPublic.lean,
Johnson/Desc/First/Look/K3CallerLayScope.lean) speak at a place x that lookAt gives and at a setting
"set" at a letter; the laws on the plan (Johnson/Desc/First/Look/K3CallerPlanesAt.lean) and the
block that sits at a link speak at placeAt. This is the line between the two.

Limits. A tie: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.LookKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

theorem placeAt_iff {X : Verify.Public} {i : Nat} {digits : Bool} {p : P} :
    placeAt X i digits = some p ↔
      ∃ x, lookAt X i digits = some x ∧ p = P.ofPlace (Params.settingOf X.P.frame) digits x := by
  unfold placeAt
  rw [Option.map_eq_some_iff]
  exact ⟨fun ⟨x, h, e⟩ => ⟨x, h, e.symm⟩, fun ⟨x, h, e⟩ => ⟨x, h, e.symm⟩⟩

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.placeAt_iff
