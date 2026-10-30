-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAtCfgRecord.lean: the entry's string at every digest, at the lines typed for the
full-size example with a record and with work.

The file holds `recordBytesAt`, `record_read_at`, `record_params_at`, `configure_record_at` and
`configure_record_read`,
over the typed values of OnBytes/Params/EntryDryRecord.lean and
OnBytes/Model/FitRecord.lean.

-/
import OnBytes.Tie.EntryPlanAtCfg
import OnBytes.Params.EntryDryRecord
import OnBytes.Model.FitRecord

set_option autoImplicit false

namespace OnBytes.Tie

/-- The parameter bytes that are spelled from the plan and the items typed for the full-size example
with a record and with work, and a digest c. -/
def recordBytesAt (c : ByteArray) : ByteArray :=
  Fmt.paramsBytes Params.recordPlan c Params.recordItems

/-- `recordBytesAt Params.recordCfg` is `Params.recordBytes`. -/
theorem recordBytesAt_recordCfg : recordBytesAt Params.recordCfg = Params.recordBytes := rfl

/-- `recordBytesAt c` is the parameter bytes in `linkAtCfg Params.recordRead c`. -/
theorem linkAtCfg_record_bytes (c : ByteArray) :
    (linkAtCfg Params.recordRead c).given.bytes = recordBytesAt c := rfl

/-- For every c of 32 bytes, the bytes spelled at c are read as those of a link's chain, and what is
read is `linkAtCfg Params.recordRead c`. -/
theorem record_read_at (c : ByteArray) (hc : c.size = 32) :
    Params.Link.read (recordBytesAt c) = some (linkAtCfg Params.recordRead c) :=
  Params.Link.read_of
    (Params.Given.read_spelled Params.recordPlan c Params.recordItems
      (Params.fit_of (by decide +kernel) hc (by decide +kernel)) (by decide +kernel))
    rfl (by decide +kernel) (by decide +kernel)

/-- At the typed lines and every digest c, the parameter bytes of an entry's chain are
`recordBytesAt c`. -/
theorem record_params_at (c : ByteArray) :
    Params.entryParams Params.recordLines c = .ok (recordBytesAt c) :=
  Params.record_params c

/-- At the typed lines, the entry's string in what `Params.configure` returns at a digest c is
`recordBytesAt c`. -/
theorem configure_record_at {x : Params.Shapes} {c : ByteArray} {bits : Nat}
    {made : Params.Configured} (h : Params.configure Params.recordLines x c bits = .ok made) :
    made.entryLink = recordBytesAt c :=
  Except.ok.inj ((Params.configure_entry h).symm.trans (record_params_at c))

/-- For c of 32 bytes that string is read as `linkAtCfg Params.recordRead c`. -/
theorem configure_record_read {x : Params.Shapes} {c : ByteArray} {bits : Nat}
    {made : Params.Configured} (hc : c.size = 32)
    (h : Params.configure Params.recordLines x c bits = .ok made) :
    Params.Link.read made.entryLink = some (linkAtCfg Params.recordRead c) := by
  rw [configure_record_at h]
  exact record_read_at c hc

/-- The tables' shape that is read there: one answer a row, 2 ^ 11 rows; so 24 bytes for each answer
of a table's record are 49,152 together. -/
theorem record_shape_at (c : ByteArray) :
    (linkAtCfg Params.recordRead c).link.table = Params.recordLink.table ∧
      24 * (Params.recordLink.table.rows * Params.recordLink.table.answers) = 49152 :=
  ⟨rfl, by decide⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.record_read_at
#print axioms OnBytes.Tie.record_params_at
#print axioms OnBytes.Tie.configure_record_read
#print axioms OnBytes.Tie.record_shape_at
