-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/Door.lean: the shapes in front of the shared chain's two proximity tests, as
terms of the chain's shape (Johnson/Desc/K14/Shape/Lin.lean: Sh2). Two definitions and two laws.
WHERE THE LIBRARY's WAY INTO SUCH A TEST (Johnson/Desc/K12/Seat.lean: enter) RETURNS THE STRUCTURE t
AT THE CHAIN's STATE d, THE SHAPE OF t (Johnson/Desc/K12/Honest/Shape/Test.lean: testSh) IS doorU
(sh2 d) AT THE TEST ON o_u's GROUP AND doorO (sh2 d) AT THE TEST ON o_omega's GROUP. That enter
returns is the laws' one premise; by its text enter asks nothing and returns at every state.

Main names:
  doorU, doorO        the shapes in front of the tests on o_u's and on o_omega's group, in the type
                      of Test.lean (TestSh): the core; the group's number; nothing passes yet; the
                      first mask, or none. Plain terms of a shape, with no default
  door_enter, door_enterO   **where enter returns the structure t at the state d, t has that
                      shape**: testSh t = doorU (sh2 d), testSh t = doorO (sh2 d). enter is taken
                      with the two functions that Seat.lean's onGu, and onGomega, hand to it: the
                      library's own way into the two tests

Its import lines: Lin.lean, Test.lean, Seat.lean.

What is not claimed. Which shape a state has where the chain comes to one of the two tests: the two
laws hold at every state d and say nothing on sh2 d. WHAT IS NOT SO: that doorO at the shape behind
"SPLIT" (Johnson/Desc/K14/Shape/End.lean: endAt) is the shape in front of the second test: the first
test stands between and changes the shape. What a proximity test asks at doorU or doorO, and that it
returns or accepts there. Nothing on soundness, on completeness or on hiding.
-/
import Johnson.Desc.K14.Shape.Lin
import Johnson.Desc.K12.Honest.Shape.Test
import Johnson.Desc.K12.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape
open OnBytes OnBytes.Params Desc.Plain
open ProofFile.Honest.Sh (TestSh testSh)

/-- The shape in front of the test on o_u's group, in the type of the proximity test's shapes
(TestSh): the core; the group's number; nothing passes yet; the first mask. -/
def doorU (e : Sh2) : TestSh := ⟨e.core, e.lin.gU, .nothing, e.lin.firstMask⟩

/-- The shape in front of the test on o_omega's group: the core; the group's number; nothing passes
yet; no mask has come. -/
def doorO (e : Sh2) : TestSh := ⟨e.core, e.lin.gOmega, .nothing, none⟩

/-- **WHERE THE LIBRARY's WAY INTO THE TEST ON o_u's GROUP RETURNS THE STRUCTURE t AT THE STATE d, t
HAS THE SHAPE doorU (sh2 d)** (Johnson/Desc/K12/Seat.lean: enter, with the two functions that onGu
hands to it). d is any state. -/
theorem door_enter (d : St) (t : VerifiableInference.Desc.K12.T12)
    (h : VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) d = .ok t) :
    testSh t = doorU (sh2 d) := by
  obtain rfl := Except.ok.inj h
  rfl

/-- The like at the test on o_omega's group: where enter, with the two functions that onGomega hands
to it, returns t at d, t has the shape doorO (sh2 d). -/
theorem door_enterO (d : St) (t : VerifiableInference.Desc.K12.T12)
    (h : VerifiableInference.Desc.K12.Seat.enter (·.gOmega) (fun _ => none) d = .ok t) :
    testSh t = doorO (sh2 d) := by
  obtain rfl := Except.ok.inj h
  rfl

end Desc.K14.Shape

#print axioms Desc.K14.Shape.door_enter
#print axioms Desc.K14.Shape.door_enterO
