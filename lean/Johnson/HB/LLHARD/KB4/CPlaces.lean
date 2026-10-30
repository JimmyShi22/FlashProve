-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/CPlaces.lean: conjunct 10 of the tests on the plan at WK: placesOk: every
block says that it stands in its own chain, and no two blocks stand at one place. By an evaluation
in Lean's kernel. A negative test: WK with the third chain's first block laid twice.
Limits. At the closed description WK alone: the test reads the blocks' places and nothing else. The
negative test bends "no two at one place"; "stands in its own chain" has none here. Nothing on
soundness.

-/
import Johnson.HB.LLHARD.KB4.WK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

theorem WK_places : WK.placesOk = true := by decide +kernel

theorem places_count : WK.places.length = 35 := by decide +kernel

/-- WK with the third chain's first block laid twice. -/
def WKtwice : FileDescription (FirstState × _root_.Desc.K14.St) :=
  { WK with second := { thirdFull with front := [thirdFull.first] } }

theorem places_bent : WKtwice.placesOk = false := by decide +kernel

end Johnson.KB4

#print axioms Johnson.KB4.WK_places
#print axioms Johnson.KB4.places_count
#print axioms Johnson.KB4.places_bent
