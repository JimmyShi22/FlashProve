-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/Pins.lean: the test `pinsFit` of a run on an entry file
(OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean) says yes at the two grounds with a record, at every digest of
the public files.

The test compares the description `entryXD G c` with the shape of the stored tables: the stored
tables' salt and the shape's are the plan's; the label is the link's; the stored trees' depth is the
shape's code's. None of the four reads the digest c.

Main names:
  `pinsFit_digest`: the test's value is the same at all digests.
  `record_pins`, `small_record_pins`: it is yes at `Tie.recordGround`, `Tie.smallRecordGround`.

Limits: two evaluations in Lean's kernel. Nothing on any file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunMain

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie (EntryGround)
open TypedOracleCompiler.Slice

/-- The test does not read the digest. -/
theorem pinsFit_digest (G : EntryGround) (sh : Params.IndexShape) (c c' : ByteArray) :
    pinsFit (entryXD G c) sh = pinsFit (entryXD G c') sh := rfl

/-- At the full-size ground with a record. -/
theorem record_pins (c : ByteArray) :
    pinsFit (entryXD OnBytes.Tie.recordGround c) OnBytes.Tie.recordGround.q.link.table = true := by
  rw [pinsFit_digest _ _ c ByteArray.empty]
  decide +kernel

/-- At the small ground with a record. -/
theorem small_record_pins (c : ByteArray) :
    pinsFit (entryXD OnBytes.Tie.smallRecordGround c)
      OnBytes.Tie.smallRecordGround.q.link.table = true := by
  rw [pinsFit_digest _ _ c ByteArray.empty]
  decide +kernel

end OnBytes.K.Left
