-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/FitRecordSmall.lean: at the lines typed for the small parameter file of the setting
"record with work", what `configure` has made for an entry's chain is typed, and is read back.

The like of OnBytes/Model/FitRecord.lean at the small example; its text but for the head was made
from that file's by a program that swaps names. If `configure` answers at `smallRecordLines`, at any
shapes, digest and bits: the link's sizes, the chain's codes and the plan as made are the typed
ones, and the plan holds in the planner's reckoning (`small_record_entry_made`); the entry's
parameter bytes as made are spelled from them (`small_record_entryLink`, `small_record_params`); the
made plan fits the format's words (`small_record_entry_fit`); and the plan as read back is the plan
as made (`small_record_entry_read`).

Main theorems: `small_record_entry_made`, `small_record_entryLink`, `small_record_entry_fit`,
`small_record_entry_read`, `small_record_params`.
What is not claimed: what the head of OnBytes/Model/FitRecord.lean does not claim, read at the small
example: above all that `configure` answers. For proofs only; the program, that is the Lean port
built from OnBytes/, does not import this file.

-/
import OnBytes.Model.FitFull
import OnBytes.Params.EntryParamsRecordSmall

set_option autoImplicit false

namespace OnBytes.Params

section
variable {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}

/-- **At `smallRecordLines`, what `configure` has made for an entry's chain is typed**: the link's
sizes (shape, table, test), the chain's codes and the plan; and the plan holds in the planner's
reckoning.
-/
theorem small_record_entry_made (h : configure smallRecordLines x cfg bits = .ok made) :
    made.sized.link = ⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩ ∧
      made.sized.entryCodes = smallRecordCodes ∧ made.entry.plan = smallRecordPlan ∧
      made.entry.holds = true := by
  obtain ⟨P, hy, hp, hh⟩ := small_record_sized
  rw [configure_entrySized h] at hy
  have e := Except.ok.inj hy
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  exact ⟨e1, e2, e3 ▸ hp, e3 ▸ hh⟩

/-- At `smallRecordLines` the entry's parameter bytes as made are spelled from the typed plan, codes
and shape: they are what `entryParams` returns at these lines and the same digest
(`small_record_params`). -/
theorem small_record_entryLink (h : configure smallRecordLines x cfg bits = .ok made) :
    made.entryLink = Fmt.paramsBytes smallRecordPlan cfg
      [("codes", spellCodes smallRecordCodes), ("the link", spellLink smallRecordLink)] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, e, _, _, _⟩ := configure_bytes h
  obtain ⟨e1, e2, e3, _⟩ := small_record_entry_made h
  rw [e, e3]
  unfold madeEntryItems
  rw [e2, e1]

/-- So the entry's made plan fits the format's words. -/
theorem small_record_entry_fit (h : configure smallRecordLines x cfg bits = .ok made) :
    made.entry.plan.fit = true := (small_record_entry_made h).2.2.1 ▸ smallRecordPlan_fit

/-- **The entry's plan as read back is the plan as made and the typed plan**; the chain's rounds as
read back are the typed entries but for the first, and the record as read back is the first. -/
theorem small_record_entry_read (h : configure smallRecordLines x cfg bits = .ok made) {q : Link}
    (hq : Link.read made.entryLink = some q) :
    q.given.plan = made.entry.plan ∧ q.given.plan = smallRecordPlan ∧
      q.given.rounds = smallRecordPlan.entries.tail ∧
      q.given.record = smallRecordPlan.entries.head? := by
  have e : q.given.plan = smallRecordPlan :=
    (entry_read_made h hq (small_record_entry_fit h)).trans (small_record_entry_made h).2.2.1
  refine ⟨entry_read_made h hq (small_record_entry_fit h), e, ?_, ?_⟩
  · show q.given.plan.rounds = _
    rw [e]
    exact smallRecordPlan_record.2
  · show (q.given.plan.entries.find? fun e => e.name == Fmt.recordName) = _
    rw [e]
    decide +kernel

end

/-- The parameter bytes of an entry's chain at `smallRecordLines` and any digest: spelled from the
typed plan, codes and shape. -/
theorem small_record_params (cfg : ByteArray) : entryParams smallRecordLines cfg =
    .ok (Fmt.paramsBytes smallRecordPlan cfg
      [("codes", spellCodes smallRecordCodes), ("the link", spellLink smallRecordLink)]) := by
  obtain ⟨P, hy, hp, _⟩ := small_record_sized
  unfold entryParams
  rw [hy]
  show (Except.ok (Fmt.paramsBytes P.plan cfg
    [("codes", spellCodes smallRecordCodes), ("the link", spellLink smallRecordLink)]) :
      Except String ByteArray) = _
  rw [hp]

end OnBytes.Params

#print axioms OnBytes.Params.small_record_entry_made
#print axioms OnBytes.Params.small_record_entryLink
#print axioms OnBytes.Params.small_record_entry_fit
#print axioms OnBytes.Params.small_record_entry_read
#print axioms OnBytes.Params.small_record_params
