-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/OwnDefs.lean: the typed groups, stages and shapes of the own test of a key of
full size, and that the shapes are what Params.laterShape makes. Definitions, and small evaluations
in Lean's kernel.

Main names.
  keyW1 and so on, keyWStages, keyWShape2 and so on, keyW2_shape and so on.

Limits. The typed values were printed by Lean's evaluator; the files beside hold them against the
planner's routines. Nothing on soundness. What the whole leaves unsaid stands in the head of
OnBytes/Params/KeyRec/Own.lean.

-/
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- The group of stage 1 of the test on the own group. -/
def keyW1 : GroupSize :=
  ⟨⟨22, 262144, 98, true⟩, ⟨13, 256, 49, true⟩, 5, 1, 1, .johnson, 158⟩

/-- The group of stage 2. -/
def keyW2 : GroupSize :=
  ⟨⟨18, 16384, 49, true⟩, ⟨15, 128, 49, true⟩, 4, 3, 1, .johnson, 277⟩

/-- The group of stage 3. -/
def keyW3 : GroupSize :=
  ⟨⟨15, 2048, 49, true⟩, ⟨14, 64, 49, true⟩, 3, 3, 1, .johnson, 423⟩

/-- The group of stage 4. -/
def keyW4 : GroupSize :=
  ⟨⟨13, 256, 41, true⟩, ⟨13, 64, 41, true⟩, 3, 3, 1, .johnson, 470⟩

/-- The group of stage 5. -/
def keyW5 : GroupSize :=
  ⟨⟨15, 256, 29, true⟩, ⟨15, 256, 29, true⟩, 0, 0, 1, .johnson, 201⟩

/-- The 5 stages of that test. -/
def keyWStages : List StageSize :=
  [⟨keyW1, 49, 0⟩, ⟨keyW2, 49, 316⟩, ⟨keyW3, 49, 109⟩, ⟨keyW4, 41, 237⟩, ⟨keyW5, 29, 5⟩]

/-- The shape from which stage 2 is solved. -/
def keyWShape2 : GroupSize :=
  ⟨⟨18, 16384, 0, true⟩, ⟨15, 128, 0, true⟩, 4, 3, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyW2_shape : laterShape recordSet keyW1 ⟨4, 3, 18, 15⟩ = keyWShape2 := by
  decide +kernel

/-- The shape from which stage 3 is solved. -/
def keyWShape3 : GroupSize :=
  ⟨⟨15, 2048, 0, true⟩, ⟨14, 64, 0, true⟩, 3, 3, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyW3_shape : laterShape recordSet keyW2 ⟨3, 3, 15, 14⟩ = keyWShape3 := by
  decide +kernel

/-- The shape from which stage 4 is solved. -/
def keyWShape4 : GroupSize :=
  ⟨⟨13, 256, 0, true⟩, ⟨13, 64, 0, true⟩, 3, 3, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyW4_shape : laterShape recordSet keyW3 ⟨3, 3, 13, 13⟩ = keyWShape4 := by
  decide +kernel

/-- The shape from which stage 5 is solved. -/
def keyWShape5 : GroupSize :=
  ⟨⟨15, 256, 0, true⟩, ⟨15, 256, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyW5_shape : laterShape recordSet keyW4 ⟨0, 0, 15, 15⟩ = keyWShape5 := by
  decide +kernel

end OnBytes.Params
