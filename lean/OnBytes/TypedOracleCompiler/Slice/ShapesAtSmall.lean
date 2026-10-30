-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesAtSmall.lean: the sizes of the small example of the setting with a record,
as a `Size` (OnBytes/TypedOracleCompiler/Slice/ShapesAt.lean).

Why. Every definition over a `Size` is one text at all sizes. A yes of the verifier on bytes is a
theorem (it does not compute). If one is to be had at all, from a run of the program and the tie, it
is at sizes at which a run is cheap; it guards the text only if it is the same text. No route to
such a yes is written. This file gives the sizes at which such a guard is to stand.

Main definition: `zSmall`: the shape of the tables in the typed small link
(`Params.smallRecordLink`, OnBytes/Params/EntryStagesRecordSmall.lean) and the radius
`Params.smallRecordRadius` (OnBytes/Params/RecordRoundSmall.lean).
Main theorems: `zSmall_T`, `zSmall_v`, `zSmall_s`, `zSmall_lg`, `zSmall_salt` (its numbers: a word
of 2^23 entries, 524288 entries of a message, 65535 random entries; 2^8 rows; one answer a row; 19
coordinates; salts of 40 bytes); `zSmall_fit` (the sizes fit: `Size.Fit`).

What is not claimed. No `Three` is given at these sizes, and no yes is shown. That the numbers are
those of any file that a program is run with: see the heads of the two files named. No probability.
Nothing on any hash function.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesAt
import OnBytes.Params.RecordRoundSmall

set_option autoImplicit false

namespace OnBytes.Slice.Shapes

/-- The sizes of the small example of the setting with a record: the tables' shape there, and
the radius in whole positions of the table's one-time test. -/
def zSmall : Size := ⟨Params.smallRecordLink.table, Params.smallRecordRadius⟩

/-- Its code: a word of 2^23 entries, 524288 entries of a message, 65535 random entries. -/
theorem zSmall_T : zSmall.T = ⟨23, 524288, 65535⟩ := rfl

/-- A table has 2^8 rows. -/
theorem zSmall_v : zSmall.v = 8 := rfl

/-- One answer a row. -/
theorem zSmall_s : zSmall.s = 1 := rfl

/-- A seed's point has 19 coordinates. -/
theorem zSmall_lg : zSmall.lg = 19 := by decide

/-- A leaf's salt has 40 bytes. -/
theorem zSmall_salt : zSmall.shape.saltBytes = 40 := rfl

/-- These sizes fit. -/
theorem zSmall_fit : zSmall.Fit where
  ok := by decide
  pos := by decide
  depth := by decide
  dim := by decide
  radius := Params.small_record_radius_inJohnson.2
  johnson := Params.small_record_radius_inJohnson.1
  pads := by decide
  cube := by
    rw [zSmall_lg]
    decide
  blocks := by
    rw [zSmall_lg, seedBS_b]
    decide

end OnBytes.Slice.Shapes
