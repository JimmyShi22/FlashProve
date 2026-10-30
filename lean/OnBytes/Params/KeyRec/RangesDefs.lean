-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/RangesDefs.lean: the typed groups, stages and shapes of the ranges' test of a
key of full size, and that the shapes are what Params.laterShape makes. Definitions, and small
evaluations in Lean's kernel.

Main names.
  keyR1 and so on, keyRStages, keyRShape2 and so on, keyR2_shape and so on.

Limits. The typed values were printed by Lean's evaluator; the files beside hold them against the
planner's routines. Nothing on soundness. What the whole leaves unsaid stands in the head of
OnBytes/Params/KeyRec/Ranges.lean.

-/
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- The group of stage 1 of the test on the group of the multiplicities. -/
def keyR1 : GroupSize :=
  ⟨⟨22, 262144, 49, false⟩, ⟨16, 4096, 49, true⟩, 4, 4, 1, .johnson, 138⟩

/-- The group of stage 2. -/
def keyR2 : GroupSize :=
  ⟨⟨19, 16384, 39, true⟩, ⟨17, 2048, 39, true⟩, 4, 3, 1, .johnson, 195⟩

/-- The group of stage 3. -/
def keyR3 : GroupSize :=
  ⟨⟨17, 2048, 33, true⟩, ⟨17, 1024, 33, true⟩, 3, 3, 1, .johnson, 210⟩

/-- The group of stage 4. -/
def keyR4 : GroupSize :=
  ⟨⟨20, 2048, 25, true⟩, ⟨20, 4096, 25, true⟩, 0, 0, 1, .johnson, 91⟩

/-- The 4 stages of that test. -/
def keyRStages : List StageSize :=
  [⟨keyR1, 49, 0⟩, ⟨keyR2, 39, 8045⟩, ⟨keyR3, 33, 3979⟩, ⟨keyR4, 25, 1949⟩]

/-- The shape from which stage 2 is solved. -/
def keyRShape2 : GroupSize :=
  ⟨⟨19, 16384, 0, true⟩, ⟨17, 2048, 0, true⟩, 4, 3, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyR2_shape : laterShape recordSet keyR1 ⟨4, 3, 19, 17⟩ = keyRShape2 := by
  decide +kernel

/-- The shape from which stage 3 is solved. -/
def keyRShape3 : GroupSize :=
  ⟨⟨17, 2048, 0, true⟩, ⟨17, 1024, 0, true⟩, 3, 3, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyR3_shape : laterShape recordSet keyR2 ⟨3, 3, 17, 17⟩ = keyRShape3 := by
  decide +kernel

/-- The shape from which stage 4 is solved. -/
def keyRShape4 : GroupSize :=
  ⟨⟨20, 2048, 0, true⟩, ⟨20, 4096, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyR4_shape : laterShape recordSet keyR3 ⟨0, 0, 20, 20⟩ = keyRShape4 := by
  decide +kernel

/-- The shape from which the first group is solved. -/
def keyRShape1 : GroupSize :=
  ⟨⟨22, 262144, 0, false⟩, ⟨16, 4096, 0, true⟩, 4, 4, 1, .johnson, 0⟩

end OnBytes.Params
