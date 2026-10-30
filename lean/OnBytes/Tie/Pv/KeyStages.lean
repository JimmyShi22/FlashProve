-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/KeyStages.lean: the five stages of the own test in a key's chains, at the full-size
lines of the setting "record with work", are in order at five typed radii.

`StageOK s g e` (OnBytes/Tie/Pv/TestPort.lean) bounds a radius from both sides. This file evaluates
two tests, `johnsonGroupTest` (OnBytes/Params/GroupPrices.lean) and `upperRadiusTest`
(OnBytes/Params/MorePrices.lean), in Lean's kernel at a typed setting and five typed groups, and
draws the condition. The two tests are written for proofs, by the planner's own arithmetic; no
planner runs them. Definitions and statements with their proofs.
Main names:
  `keySet`: the setting, typed: the target 128, one sample, and 20, 28 and 32 bits of work before
    the draws of positions.
  `ownG1` to `ownG5`, `ownStages`: the five groups and stages, typed.
  `own_group_test`, `own_upper_test`: the two tests answer yes at the five groups, each at its
    radius: 3138896, 196275, 24460, 6631 and 29702 positions.
  `ownRadius`: these radii as a function of the group; 0 for any other group.
  `own_stages_ok`: `StageOK keySet x.g (ownRadius x.g)` for every stage x of `ownStages`.
  `key_field`: the field of `keySet` has two elements at least.
  `own_test_covered`: so the counts `testPairs` of the own test are covered, pair by pair, by the
    planner's list, if `close` has tested every round.
Whence the numbers: `keySet` is typed after `recordSet` (OnBytes/Params/EntryStagesRecord.lean). By
that file's head `recordSet` is typed for what the first 32 lines of policy.txt of the example set
prover/examples/target_full_f2 say. That `keySet` and `recordSet` are equal is not shown here. The
five groups, and the two numbers beside each, are copied from files on a key's own test that are not
in this library. By their heads these values were printed by Lean's evaluator of the planner, at
`recordSet` and at sizes of a key that these files type, and are checked there in Lean's kernel.
Whence these sizes are is not known here. A program has held the five groups, but not the two
numbers beside each, sign for sign against a print of the planner's own analysis of the groups that
a key's plan names. The print was made by evaluating this library's port of the planner at the three
public files of the example set prover/examples/target_full_f2, held as constants by the program
that printed:
  policy.txt (2,629 bytes), sha256
    ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae
  layout.txt (224,975 bytes), sha256
    a99b964bbd3648d6e3b4007fc9370b5c70c7e9668848daa039820bc9e03e8f80
  KL.bin (2,784 bytes), sha256
    1c3191164c5113fd04d5108a469d7b3d17f4ccb3256e8a676d15bdc94435b919
That program and the program that held the groups against the print are not in this repository. The
radii are those of Johnson/Top/H/KeyValues.lean; `own_group_test` and `own_upper_test` hold them
against the planner's own functions.
Limits: that the typed setting and groups are those of a key's plan is not shown here. The radii
were reckoned outside Lean; the tests check them: the first asks that a radius is at most the lower
end of the planner's interval, rounded down, the second that it is at least the upper end, rounded
down, so at each of the five the two ends agree. Nothing on what a price is worth under the rule of
the Johnson radius. The other three tests of a key's chains are not treated.

See also: `keySet` is typed here, and not imported from OnBytes/Params/EntryStagesRecord.lean, so
that this file imports nothing beyond the file named below.
-/
import OnBytes.Tie.Pv.TestPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open OnBytes OnBytes.Params

/-- The setting. -/
def keySet : Setting where
  target := 128
  printed := true
  rowsFactor := false
  samples := 1
  saltBytes := 40
  positionBytes := 0
  workField := ⟨0, 0, 0⟩
  workSample := ⟨0, 0, 0⟩
  workCloseness := ⟨0, 0, 0⟩
  workQuery := ⟨20, 28, 32⟩
  workSmall := ⟨0, 0, 0⟩

/-- The groups of the five stages of the own test. -/
def ownG1 : GroupSize :=
  ⟨⟨22, 262144, 98, true⟩, ⟨13, 256, 49, true⟩, 5, 1, 1, .johnson, 158⟩
def ownG2 : GroupSize :=
  ⟨⟨18, 16384, 49, true⟩, ⟨15, 128, 49, true⟩, 4, 3, 1, .johnson, 277⟩
def ownG3 : GroupSize :=
  ⟨⟨15, 2048, 49, true⟩, ⟨14, 64, 49, true⟩, 3, 3, 1, .johnson, 423⟩
def ownG4 : GroupSize :=
  ⟨⟨13, 256, 41, true⟩, ⟨13, 64, 41, true⟩, 3, 3, 1, .johnson, 470⟩
def ownG5 : GroupSize :=
  ⟨⟨15, 256, 29, true⟩, ⟨15, 256, 29, true⟩, 0, 0, 1, .johnson, 201⟩

/-- The stages of the own test. -/
def ownStages : List StageSize :=
  [⟨ownG1, 49, 0⟩, ⟨ownG2, 49, 316⟩, ⟨ownG3, 49, 109⟩, ⟨ownG4, 41, 237⟩, ⟨ownG5, 29, 5⟩]

theorem own_group_test :
    johnsonGroupTest keySet ownG1 3138896 = true ∧
      johnsonGroupTest keySet ownG2 196275 = true ∧
      johnsonGroupTest keySet ownG3 24460 = true ∧
      johnsonGroupTest keySet ownG4 6631 = true ∧
      johnsonGroupTest keySet ownG5 29702 = true := by decide +kernel

theorem own_upper_test :
    upperRadiusTest keySet ownG1 3138896 = true ∧
      upperRadiusTest keySet ownG2 196275 = true ∧
      upperRadiusTest keySet ownG3 24460 = true ∧
      upperRadiusTest keySet ownG4 6631 = true ∧
      upperRadiusTest keySet ownG5 29702 = true := by decide +kernel

/-- From a yes of both tests. -/
theorem stageOK_of_tests {s : Setting} {g : GroupSize} {e : ℕ}
    (h : johnsonGroupTest s g e = true) (h' : upperRadiusTest s g e = true) : StageOK s g e :=
  ⟨johnsonGroup_of_test h, (upperRadius_of_test h').1, (upperRadius_of_test h').2⟩

/-- The radii of the five groups. -/
def ownRadius (g : GroupSize) : ℕ :=
  if g = ownG1 then 3138896 else if g = ownG2 then 196275 else if g = ownG3 then 24460
  else if g = ownG4 then 6631 else if g = ownG5 then 29702 else 0

theorem ownRadius_at :
    ownRadius ownG1 = 3138896 ∧ ownRadius ownG2 = 196275 ∧ ownRadius ownG3 = 24460 ∧
      ownRadius ownG4 = 6631 ∧ ownRadius ownG5 = 29702 := by decide +kernel

/-- Every stage of the own test is in order at its radius. -/
theorem own_stages_ok : ∀ x ∈ ownStages, StageOK keySet x.g (ownRadius x.g) := by
  intro x hx
  simp only [ownStages, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · show StageOK keySet ownG1 (ownRadius ownG1)
    rw [ownRadius_at.1]
    exact stageOK_of_tests own_group_test.1 own_upper_test.1
  · show StageOK keySet ownG2 (ownRadius ownG2)
    rw [ownRadius_at.2.1]
    exact stageOK_of_tests own_group_test.2.1 own_upper_test.2.1
  · show StageOK keySet ownG3 (ownRadius ownG3)
    rw [ownRadius_at.2.2.1]
    exact stageOK_of_tests own_group_test.2.2.1 own_upper_test.2.2.1
  · show StageOK keySet ownG4 (ownRadius ownG4)
    rw [ownRadius_at.2.2.2.1]
    exact stageOK_of_tests own_group_test.2.2.2.1 own_upper_test.2.2.2.1
  · show StageOK keySet ownG5 (ownRadius ownG5)
    rw [ownRadius_at.2.2.2.2]
    exact stageOK_of_tests own_group_test.2.2.2.2 own_upper_test.2.2.2.2

theorem key_field : 2 ≤ keySet.cardE := by decide +kernel

/-- The counts of the own test are covered by the planner's list. -/
theorem own_test_covered (rows fm : ℕ) (mr : Bool)
    (hg : ∀ y ∈ ioppList keySet .once ownStages rows fm mr, y.Good keySet .once) :
    List.Forall₂ (Covered keySet .once) (testPairs keySet ownRadius ownStages rows)
      (ioppList keySet .once ownStages rows fm mr) :=
  test_covered key_field ownRadius ownStages rows fm mr own_stages_ok hg

end Cb.Pv.Tower

#print axioms Cb.Pv.Tower.own_group_test
#print axioms Cb.Pv.Tower.own_upper_test
#print axioms Cb.Pv.Tower.own_stages_ok
#print axioms Cb.Pv.Tower.own_test_covered
