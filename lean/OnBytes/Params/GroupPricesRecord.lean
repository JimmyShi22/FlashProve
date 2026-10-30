-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/GroupPricesRecord.lean: the five groups of the proximity test in an entry's chain, at
the full-size lines of the setting "record with work", meet the conditions of
OnBytes/Params/GroupPrices.lean.

`JohnsonGroup s g e` (OnBytes/Params/GroupPrices.lean) gathers the conditions under which the prices
of a fold's rounds and of a last step's first round cover the proof library's numbers. This file
evaluates the test `johnsonGroupTest` in Lean's kernel at `recordSet` and the five typed groups
`recordG1` to `recordG5` (OnBytes/Params/EntryStagesRecord.lean), each at a typed radius: 8342420,
1569886, 98104, 6044 and 13370 positions (`record_groups_test`), and draws the conditions
(`record_groups_johnson`). The planner makes these groups (`record_group`, `record_stage2` to
`record_stage5`). The law on a fold's rounds is for stages 1 to 4, with 8, 5, 4 and 4 rounds; at
stage 1, where h = 0, no round has a term for the mask rows. The law on the last step is for stage
5, which has no fold. The prices of these 21 rounds and of that one are not marked bad
(`record_prices_good`). The radii were printed by Lean's evaluator as the lower end of each group's
distance times the length, rounded down; the test asks that a radius is at most that number.

Main theorems: `record_groups_test`, `record_groups_johnson`, `record_prices_good`.
What is not claimed: what the head of OnBytes/Params/GroupPrices.lean does not claim. That a typed
radius is the largest that meets the test. The groups of a key's and of a proof's tests, and the
small files. For proofs only; the program, that is the Lean port built from OnBytes/, does
not import this file.

-/
import OnBytes.Params.GroupPrices
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false

namespace OnBytes.Params

/-- At the five groups of the proximity test in an entry's chain, at the full-size lines of the
setting "record with work", the test answers yes, each at its typed radius. -/
theorem record_groups_test :
    johnsonGroupTest recordSet recordG1 8342420 = true ∧
      johnsonGroupTest recordSet recordG2 1569886 = true ∧
      johnsonGroupTest recordSet recordG3 98104 = true ∧
      johnsonGroupTest recordSet recordG4 6044 = true ∧
      johnsonGroupTest recordSet recordG5 13370 = true := by decide +kernel

/-- So the five groups meet the conditions. -/
theorem record_groups_johnson :
    JohnsonGroup recordSet recordG1 8342420 ∧ JohnsonGroup recordSet recordG2 1569886 ∧
      JohnsonGroup recordSet recordG3 98104 ∧ JohnsonGroup recordSet recordG4 6044 ∧
      JohnsonGroup recordSet recordG5 13370 :=
  ⟨johnsonGroup_of_test record_groups_test.1, johnsonGroup_of_test record_groups_test.2.1,
    johnsonGroup_of_test record_groups_test.2.2.1, johnsonGroup_of_test record_groups_test.2.2.2.1,
    johnsonGroup_of_test record_groups_test.2.2.2.2⟩

/-- The prices of the 21 rounds of the four folds and of the last step's first round are not marked
bad. -/
theorem record_prices_good :
    ((List.range' 1 8).all fun j =>
        !(foldRoundError recordSet recordG1 (analysisOfM recordSet recordG1) j).bad) = true ∧
      ((List.range' 1 5).all fun j =>
        !(foldRoundError recordSet recordG2 (analysisOfM recordSet recordG2) j).bad) = true ∧
      ((List.range' 1 4).all fun j =>
        !(foldRoundError recordSet recordG3 (analysisOfM recordSet recordG3) j).bad) = true ∧
      ((List.range' 1 4).all fun j =>
        !(foldRoundError recordSet recordG4 (analysisOfM recordSet recordG4) j).bad) = true ∧
      (baseError recordSet recordG5 (analysisOfM recordSet recordG5)).bad = false := by
  decide +kernel

end OnBytes.Params

#print axioms OnBytes.Params.record_prices_good
#print axioms OnBytes.Params.record_groups_test
#print axioms OnBytes.Params.record_groups_johnson
