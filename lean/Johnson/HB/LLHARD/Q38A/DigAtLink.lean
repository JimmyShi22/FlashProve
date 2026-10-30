-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38A/DigAtLink.lean: the place that the lookups' reader of the digits gives at
segment l bears the number l.

  `digAt_link`: from `Look.digAt X l = some (x, tl)` (Johnson/Desc/First/Look/K3CallerTests.lean):
    `x.link = l`. By `lookAt_link` (Johnson/Desc/First/Look/K3CallsAddress.lean), through two binds
    and a map.

Limits. General: no public file, no written value, no head of conditions is read. Nothing on
soundness.
-/
import Johnson.Desc.First.Look.K3CallerTests
import Johnson.Desc.First.Look.K3CallsAddress

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First

/-- **The digits' place at segment l bears the number l.** -/
theorem digAt_link {X : Verify.Public} {l : ℕ} {x : Look.Place} {tl : HTailF2}
    (hx : Look.digAt X l = some (x, tl)) : x.link = l := by
  unfold Look.digAt at hx
  obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨tl', _, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨f9, _, hx⟩ := Option.map_eq_some_iff.1 hx
  obtain rfl : x' = x := congrArg Prod.fst hx
  exact VerifiableInference.OnPublicFiles.lookAt_link h1

end Q38

#print axioms Q38.digAt_link
