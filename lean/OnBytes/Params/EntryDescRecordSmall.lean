-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryDescRecordSmall.lean: the description of an entry's chain at the small files of
the setting "record with work", for all tables; and what `configure` has made is read whole.

The like of the last two theorems of OnBytes/Params/EntryDescRecord.lean, whose general laws it
uses, at the small example. Under `smallRecordRead` and for all tables, a description that
`Tie.entrySpec` gives is made of the typed parameter bytes, the rounds `smallRecordRounds` and the
link's statement (`small_record_entrySpec_all`). At `smallRecordLines` and the typed digest the
bytes that `configure` has made for an entry's chain are `smallRecordBytes`, and `Link.read` returns
`smallRecordRead` on them (`small_record_made_read`). The table's shape in the typed link is written
out, at both sizes (`recordLink_table`, `smallRecordLink_table`).

Main theorems: `small_record_entrySpec_all`, `small_record_made_read`, `recordLink_table`,
`smallRecordLink_table`.
What is not claimed: what the head of OnBytes/Params/EntryDescRecord.lean does not claim, read at
the small example: above all that `Tie.entrySpec` gives a description, and that `configure` answers.
For proofs only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.EntryDescRecord
import OnBytes.Params.EntryDryRecordSmall
import OnBytes.Model.FitRecordSmall

set_option autoImplicit false

namespace OnBytes.Params

/-- **Under `smallRecordRead` and for all tables**: a description that `Tie.entrySpec` gives is made
of the typed parameter bytes, the rounds `smallRecordRounds` and the statement. Nothing says that it
gives one. -/
theorem small_record_entrySpec_all {first further : TableName} {block : Blk Unit} {S : Fmt.SpecX}
    (h : Tie.entrySpec smallRecordRead first further = some (block, S)) :
    S = entrySpecOf smallRecordRead smallRecordRounds (Link.statement first further) :=
  small_record_entrySpec (linkDryBySizes smallRecordLink) h

/-- **At `smallRecordLines` and the typed digest, what `configure` has made for an entry's chain is
read whole**: the made bytes are `smallRecordBytes`, and `Link.read` returns `smallRecordRead` on
them: the typed plan, digest, items, codes and shape. -/
theorem small_record_made_read {x : Shapes} {bits : Nat} {made : Configured}
    (h : configure smallRecordLines x smallRecordCfg bits = .ok made) :
    made.entryLink = smallRecordBytes ∧ Link.read made.entryLink = some smallRecordRead := by
  have e : made.entryLink = smallRecordBytes := small_record_entryLink h
  exact ⟨e, e ▸ small_record_read⟩

/-- The shape of the tables in the full-size link: the code (length 2 ^ 32, 402653184 entries of a
message, 44040191 random entries), 11 row variables, one answer a row, salts of 40 bytes. -/
theorem recordLink_table : recordLink.table = ⟨⟨32, 402653184, 44040191⟩, 11, 1, 40⟩ := rfl

/-- The shape of the tables in the small link: the code (length 2 ^ 23, 524288 entries of a message,
65535 random entries), 8 row variables, one answer a row, salts of 40 bytes. -/
theorem smallRecordLink_table : smallRecordLink.table = ⟨⟨23, 524288, 65535⟩, 8, 1, 40⟩ := rfl

end OnBytes.Params

#print axioms OnBytes.Params.small_record_entrySpec_all
#print axioms OnBytes.Params.small_record_made_read
#print axioms OnBytes.Params.recordLink_table
#print axioms OnBytes.Params.smallRecordLink_table
