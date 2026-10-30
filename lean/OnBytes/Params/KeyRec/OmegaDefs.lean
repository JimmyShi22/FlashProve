-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/OmegaDefs.lean: the typed groups, stages and shapes of Omega's test of a key
of full size, and that the shapes are what Params.laterShape makes. Definitions, and small
evaluations in Lean's kernel.

Main names.
  keyO1 and so on, keyOStages, keyOShape2 and so on, keyO2_shape and so on.

Limits. The typed values were printed by Lean's evaluator; the files beside hold them against the
planner's routines. Nothing on soundness. What the whole leaves unsaid stands in the head of
OnBytes/Params/KeyRec/Omega.lean.

-/
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- The group of stage 1 of the test on Omega's group. -/
def keyO1 : GroupSize :=
  ⟨⟨22, 262144, 98, true⟩, ⟨13, 64, 146, true⟩, 4, 0, 1, .johnson, 158⟩

/-- The group of stage 2. -/
def keyO2 : GroupSize :=
  ⟨⟨18, 16384, 49, true⟩, ⟨14, 128, 49, true⟩, 4, 3, 1, .johnson, 277⟩

/-- The group of stage 3. -/
def keyO3 : GroupSize :=
  ⟨⟨14, 1024, 49, true⟩, ⟨13, 64, 49, true⟩, 4, 3, 1, .johnson, 489⟩

/-- The group of stage 4. -/
def keyO4 : GroupSize :=
  ⟨⟨15, 1024, 39, true⟩, ⟨15, 512, 39, true⟩, 0, 0, 1, .johnson, 345⟩

/-- The 4 stages of that test. -/
def keyOStages : List StageSize :=
  [⟨keyO1, 49, 0⟩, ⟨keyO2, 49, 506⟩, ⟨keyO3, 49, 109⟩, ⟨keyO4, 39, 237⟩]

/-- The shape from which stage 2 is solved. -/
def keyOShape2 : GroupSize :=
  ⟨⟨18, 16384, 0, true⟩, ⟨14, 128, 0, true⟩, 4, 3, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyO2_shape : laterShape recordSet keyO1 ⟨4, 3, 18, 14⟩ = keyOShape2 := by
  decide +kernel

/-- The shape from which stage 3 is solved. -/
def keyOShape3 : GroupSize :=
  ⟨⟨14, 1024, 0, true⟩, ⟨13, 64, 0, true⟩, 4, 3, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyO3_shape : laterShape recordSet keyO2 ⟨4, 3, 14, 13⟩ = keyOShape3 := by
  decide +kernel

/-- The shape from which stage 4 is solved. -/
def keyOShape4 : GroupSize :=
  ⟨⟨15, 1024, 0, true⟩, ⟨15, 512, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyO4_shape : laterShape recordSet keyO3 ⟨0, 0, 15, 15⟩ = keyOShape4 := by
  decide +kernel

end OnBytes.Params
