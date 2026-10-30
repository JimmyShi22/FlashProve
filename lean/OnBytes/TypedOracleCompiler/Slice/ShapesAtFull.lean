-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesAtFull.lean: the sizes of the full-size parameter file with a record, as a
`Size` (OnBytes/TypedOracleCompiler/Slice/ShapesAt.lean).



Main definition: `zFull`: the shape `recShape` (OnBytes/Slice/RecordFull.lean) and the radius
`Params.recordRadius` (OnBytes/Params/RecordRound.lean).
Main theorems.
 `zFull_T`, `zFull_v`, `zFull_s`, `zFull_lg`, `zFull_D`   its numbers are those of
                       OnBytes/Slice/RecordFull.lean; its decoder's data are `decRecFull` at that
                       radius.
 `zFull_shape`, `zFull_fit`   its shape is the typed full-size link's; the sizes fit (`Size.Fit`).








What is not claimed. That the numbers are those of any file that a program is run with: see the
head of OnBytes/Slice/RecordFull.lean. No `Three` is given. No probability. Nothing on any
hash function.







Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesAt
import OnBytes.Slice.RawWalks
import OnBytes.Slice.SeedStrings
import OnBytes.Params.RecordRound

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open _root_.Iop Rom _root_.Run Compile
open OnBytes.Tie (IdKey idCode firstId)

/-- The sizes of the full-size parameter file with a record: the tables' shape there, and the
radius in whole positions of the table's one-time test. -/
def zFull : Size := ⟨recShape, Params.recordRadius⟩

/-- Its code is `recT`. -/
theorem zFull_T : zFull.T = recT := rfl

/-- Its number of row variables is `recV`. -/
theorem zFull_v : zFull.v = recV := rfl

/-- Its answers a row are `recS`. -/
theorem zFull_s : zFull.s = recS := rfl

/-- Its coordinates of a seed's point are `recLg`. -/
theorem zFull_lg : zFull.lg = recLg := recShape_cubeBits

/-- Its decoder's data are those of OnBytes/Slice/RecordFull.lean at the radius. -/
theorem zFull_D : zFull.D = decRecFull Params.recordRadius := by
  show decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s = decRec recT recV _ recLg recS
  rw [zFull_lg]
  rfl

/-- Its shape is the shape of the tables in the typed full-size link. -/
theorem zFull_shape : zFull.shape = Params.recordLink.table := rfl

/-- These sizes fit. -/
theorem zFull_fit : zFull.Fit where
  ok := recShape_ok
  pos := by decide
  depth := by decide
  dim := by decide
  radius := Params.record_radius_inJohnson.2
  johnson := Params.record_radius_inJohnson.1
  pads := recT_room.1
  cube := by
    rw [zFull_lg]
    exact recT_room.2
  blocks := by
    rw [zFull_lg]
    show (seedBS recLg recS).b + 1 < 2 ^ 48
    rw [seedBS_b_full]
    decide

/-! -/

/-! -/

end OnBytes.Slice.Shapes
