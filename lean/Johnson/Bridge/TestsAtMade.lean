-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/TestsAtMade.lean: THE NINE PROXIMITY TESTS THAT ARE MADE OF THE WRITTEN PLAN ARE THE
NINE WRITTEN TESTS OF THE FULL SIZE, WHOLE, IN ANOTHER ORDER.
By Lean's kernel.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Why. Johnson/Bridge/TestsAtWritten.lean's `testsFull` is a written list: its stages, radii and bits
of work were read off prints of the planner's functions, its brackets reckoned outside Lean; its
head says that no theorem ties them to a plan. `planTestsBy Rad.planner M`
(Johnson/Bridge/PlanTests.lean) makes nine tests of a plan M: the stages' sizes and the bits of work
are TAKEN OVER from M; the radii are COMPUTED by the planner's own analysis; the brackets are
COMPUTED by this folder's `brOf`. Johnson/Goal/Written/Made.lean's `writtenMade` is the written form
of what the planner configures at the full size, but for the eight fields that hang on the digest of
the public files. Here the two meet: so whoever has `freeOf M = writtenMade` of a plan M has the
nine written tests as M's own.

Main names:
  `tests_free`: the made tests do not hang on the eight fields that hang on the digest. By rfl.
  `madeTests_written`: **`planTestsBy Rad.planner (writtenMade.at Hung.none) = testsFull.drop 5 ++
    testsFull.take 5`**: stages, radii, bits of work and brackets. By `decide` with the kernel.
  `tests_of_free`: SO: from `freeOf M = writtenMade`: the same of M.
  `mem_tests_of_free`: a test is one of M's nine just if it is one of the nine written.

The order. The made list has the proof file's four tests first, then the key file's four, then the
entry file's; the written list has the key file's four, the entry file's, then the proof file's.

Limits. THAT `freeOf M = writtenMade` HOLDS OF THE PLAN THAT A VERIFIER MAKES OF ANY FILES IS NOT
SAID HERE: it is a premise, meant for a test that the verifier asks: IT IS THE WHOLE TIE TO A FILE:
until a verifier asks it the tie reaches no file. Both sides' numerals come off prints of this
library's own planner: the limits of Johnson/Goal/Written/Made.lean hold. So do those of
Johnson/Bridge/PlanTests.lean: which bits of work belong to which test is BY ORDER ALONE; what is
over nine on either side of its zipWith is dropped in silence; the radii are whatever the rule says,
and no rule is tied to a protocol here. THE LINKS' GROUPS ARE IN NONE OF THE NINE: `foldFull`'s
places 18 and 19 stay untied: of its 36 places 34 are carried. `planTestsB M = true` does not
follow. The full size alone: nothing on `testsSmall`. That a block at a seat takes its numbers from
one of these tests is not said here. The five instances of decidable equality are this file's own,
made by Lean's deriving handler. Nothing on soundness.

-/
import Johnson.Goal.Written.Made
import Johnson.Bridge.PlanTests
import Johnson.Bridge.TestsAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Johnson.Bridge.AtMade
open OnBytes OnBytes.Params OnBytes.Slice Johnson.Bridge Johnson.G.MadeFree
open VerifiableInference.PlanWritten.Joined (writtenMade)

deriving instance DecidableEq for OnBytes.Slice.Sg
deriving instance DecidableEq for Johnson.Bridge.Br
deriving instance DecidableEq for Johnson.Bridge.FoldedPlace
deriving instance DecidableEq for Johnson.Bridge.LastPlace
deriving instance DecidableEq for Johnson.Bridge.TestAt

/-- The made tests do not hang on the eight fields that hang on the digest. -/
theorem tests_free (W : Free) (h h' : Hung) :
    planTestsBy Rad.planner (W.at h) = planTestsBy Rad.planner (W.at h') := rfl

/-- **The nine tests made of the written plan are the nine written tests, whole.** -/
theorem madeTests_written :
    planTestsBy Rad.planner (writtenMade.at Hung.none) = testsFull.drop 5 ++ testsFull.take 5 := by
  decide +kernel

/-- **So of every plan whose four free fields are the written ones.** -/
theorem tests_of_free {M : Configured} (h : freeOf M = writtenMade) :
    planTestsBy Rad.planner M = testsFull.drop 5 ++ testsFull.take 5 := by
  rw [← at_free M, h]
  exact (tests_free _ _ _).trans madeTests_written

/-- A test is one of such a plan's nine just if it is one of the nine written. -/
theorem mem_tests_of_free {M : Configured} (h : freeOf M = writtenMade) (T : TestAt) :
    T ∈ planTestsBy Rad.planner M ↔ T ∈ testsFull := by
  rw [tests_of_free h, List.mem_append]
  constructor
  · rintro (h1 | h1)
    · exact List.mem_of_mem_drop h1
    · exact List.mem_of_mem_take h1
  · intro h1
    rw [← List.take_append_drop 5 testsFull, List.mem_append] at h1
    exact h1.symm

end Johnson.Bridge.AtMade

#print axioms Johnson.Bridge.AtMade.tests_free
#print axioms Johnson.Bridge.AtMade.madeTests_written
#print axioms Johnson.Bridge.AtMade.tests_of_free
#print axioms Johnson.Bridge.AtMade.mem_tests_of_free
