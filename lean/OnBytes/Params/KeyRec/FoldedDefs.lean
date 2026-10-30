-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/FoldedDefs.lean: the typed groups, stages and shapes of the folded row's test
of a key of full size, and that the shapes are what Params.laterShape makes. Definitions, and small
evaluations in Lean's kernel.

Main names.
  keyU1 and so on, keyUStages, keyUShape2 and so on, keyU2_shape and so on.

Limits. The typed values were printed by Lean's evaluator; the files beside hold them against the
planner's routines. Nothing on soundness. What the whole leaves unsaid stands in the head of
OnBytes/Params/KeyRec/Folded.lean.

-/
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- The group of stage 1 of the test on the folded row's group. -/
def keyU1 : GroupSize :=
  ⟨⟨24, 4194304, 97, true⟩, ⟨13, 64, 146, true⟩, 7, 0, 1, .johnson, 182⟩

/-- The group of stage 2. -/
def keyU2 : GroupSize :=
  ⟨⟨21, 131072, 52, true⟩, ⟨12, 256, 52, true⟩, 5, 2, 1, .johnson, 167⟩

/-- The group of stage 3. -/
def keyU3 : GroupSize :=
  ⟨⟨17, 8192, 52, true⟩, ⟨12, 256, 52, true⟩, 4, 2, 1, .johnson, 292⟩

/-- The group of stage 4. -/
def keyU4 : GroupSize :=
  ⟨⟨13, 512, 52, true⟩, ⟨12, 256, 52, true⟩, 4, 2, 1, .johnson, 509⟩

/-- The group of stage 5. -/
def keyU5 : GroupSize :=
  ⟨⟨14, 512, 49, true⟩, ⟨14, 1024, 49, true⟩, 0, 0, 1, .johnson, 489⟩

/-- The 5 stages of that test. -/
def keyUStages : List StageSize :=
  [⟨keyU1, 97, 0⟩, ⟨keyU2, 52, 507⟩, ⟨keyU3, 52, 356⟩, ⟨keyU4, 52, 356⟩, ⟨keyU5, 49, 356⟩]

/-- The shape from which stage 2 is solved. -/
def keyUShape2 : GroupSize :=
  ⟨⟨21, 131072, 0, true⟩, ⟨12, 256, 0, true⟩, 5, 2, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyU2_shape : laterShape recordSet keyU1 ⟨5, 2, 21, 12⟩ = keyUShape2 := by
  decide +kernel

/-- The shape from which stage 3 is solved. -/
def keyUShape3 : GroupSize :=
  ⟨⟨17, 8192, 0, true⟩, ⟨12, 256, 0, true⟩, 4, 2, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyU3_shape : laterShape recordSet keyU2 ⟨4, 2, 17, 12⟩ = keyUShape3 := by
  decide +kernel

/-- The shape from which stage 4 is solved. -/
def keyUShape4 : GroupSize :=
  ⟨⟨13, 512, 0, true⟩, ⟨12, 256, 0, true⟩, 4, 2, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyU4_shape : laterShape recordSet keyU3 ⟨4, 2, 13, 12⟩ = keyUShape4 := by
  decide +kernel

/-- The shape from which stage 5 is solved. -/
def keyUShape5 : GroupSize :=
  ⟨⟨14, 512, 0, true⟩, ⟨14, 1024, 0, true⟩, 0, 0, 1, .johnson, 0⟩

/-- It is the shape that `laterShape` makes. -/
theorem keyU5_shape : laterShape recordSet keyU4 ⟨0, 0, 14, 14⟩ = keyUShape5 := by
  decide +kernel

end OnBytes.Params
