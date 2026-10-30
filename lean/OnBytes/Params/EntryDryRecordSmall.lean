-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryDryRecordSmall.lean: parameter bytes typed for an entry's chain at the small
files of the setting "record with work", read; the chain's rounds, written; and a yardstick: the dry
run of the Lean port's link states these rounds.

The like of OnBytes/Params/EntryDryRecord.lean at the small example; its text but for the head was
made from that file's by a program that swaps names, the word for the size, the digest and four
numbers. The parameter bytes `smallRecordBytes` are spelled from the plan, codes and link's shape
typed in OnBytes/Params/EntryStagesRecordSmall.lean and from a typed digest, `smallRecordCfg`. They
are the bytes that `entryParams` returns at `smallRecordLines` and that digest
(`small_record_bytes`). They are read as those of a link's chain (`small_record_read`). The typed
shape says that tables have 2 ^ 8 rows and a record of one answer a row (`small_record_answers`).
The rounds of the chain, each with the stored trees that it opens, are WRITTEN
(`smallRecordRounds`): by the format's own makers of rounds at a typed record of sizes
(`smallRecordPar`, `smallRecordFmt`, `smallRecordStored`); no run of a program stands in that term.
There are 24 of them (`small_record_rounds_length`): as many as the plan has entries but for the
entry RECORD (`small_record_rounds_all`). A YARDSTICK: the dry run of the link's block at two keys
of zeros of these sizes returns rounds (`small_record_dry`), and they are the written ones
(`small_record_rounds`). A description that `Tie.entrySpec` gives under these bytes is made of these
parameter bytes, these rounds and the link's statement on the two tables, under the hypothesis
`LinkDryBySizes smallRecordLink` (`small_record_entrySpec`);
OnBytes/Params/EntryDescRecordSmall.lean takes the hypothesis away.

Main definitions: `smallRecordCfg`, `smallRecordItems`, `smallRecordBytes`, `smallRecordRead`,
`smallRecordPar`, `smallRecordFmt`, `smallRecordStored`, `smallRecordRounds`.
Main theorems: `small_record_bytes`, `small_record_read`, `small_record_answers`,
`small_record_dry`, `small_record_rounds`, `small_record_rounds_length`,
`small_record_rounds_all`, `small_record_entrySpec`.
What is not claimed: what the head of OnBytes/Params/EntryDryRecord.lean does not claim, read at the
small example. That the digest of any three public files is `smallRecordCfg`: a test computes that
value from copies of three files (a test that is not in this library, over a file of copies that is
not in it either, whose head says where it is from); the same test has
`Tie.entrySpec` give a description at two made-up tables. For proofs only; the program, that is the
Lean port built from OnBytes/, does not import this file.


-/
import OnBytes.Params.EntryRoundsToy
import OnBytes.Params.EntryParamsRecordSmall
import OnBytes.Params.EntryRoundsRecord
import OnBytes.Params.Spell
import OnBytes.Params.ToyDescriptions

set_option autoImplicit false

namespace OnBytes.Params

/-- A digest typed for three small public files of the setting. -/
def smallRecordCfg : ByteArray :=
  Fmt.unhex "ee76db0af2ce5af0a9b9d27398aac0adfafc2c5a4c2fb5643bb6a9bcb2535a56"

/-- The two items after the digest. -/
def smallRecordItems : List (String × ByteArray) :=
  [("codes", spellCodes smallRecordCodes), ("the link", spellLink smallRecordLink)]

/-- The parameter bytes that are spelled from the typed plan, digest, codes and shape. -/
def smallRecordBytes : ByteArray := Fmt.paramsBytes smallRecordPlan smallRecordCfg smallRecordItems

/-- What the parameter bytes hold as those of a link's chain. -/
def smallRecordRead : Link :=
  ⟨⟨smallRecordBytes, smallRecordPlan, smallRecordCfg, smallRecordItems⟩, smallRecordCodes,
    smallRecordLink⟩

/-- At `smallRecordLines` and the typed digest the parameter bytes of an entry's chain are
`smallRecordBytes`. -/
theorem small_record_bytes :
    entryParams smallRecordLines smallRecordCfg = .ok smallRecordBytes := by
  obtain ⟨P, hy, hp, _⟩ := small_record_sized
  unfold entryParams
  rw [hy]
  show (Except.ok (Fmt.paramsBytes P.plan smallRecordCfg smallRecordItems) :
    Except String ByteArray) = _
  rw [hp]
  rfl

/-- The parameter bytes `smallRecordBytes` are read as those of a link's chain. -/
theorem small_record_read : Link.read smallRecordBytes = some smallRecordRead :=
  Link.read_of
    (Given.read_spelled smallRecordPlan smallRecordCfg smallRecordItems
      (fit_of (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel))
    rfl (by decide +kernel) (by decide +kernel)

/-- The shape that is typed says that tables have a record of one answer a row, and 2 ^ 8 rows. -/
theorem small_record_answers :
    smallRecordRead.link.table.answers = 1 ∧ smallRecordRead.link.table.rows = 256 := by
  decide +kernel

/-- Under `smallRecordRead` the dry run of the link's block, the Lean port's, at keys of zeros
returns rounds. -/
theorem small_record_dry : (entryRoundsAny smallRecordRead).isSome = true := by decide +kernel

/-- The format's record of sizes at these files, typed. -/
def smallRecordPar : Fmt.M3.Par where
  fld := .two
  T := ⟨23, 524288, 65535⟩
  v := 8
  s := 1
  nu0 := 51
  nuj := 51
  C := ⟨17, 32768, 97⟩
  Z := ⟨13, 64, 97⟩
  R := 18
  stages := [⟨⟨17, 32768, 97⟩, ⟨13, 64, 97⟩, 6, 0, 97⟩,
    ⟨⟨14, 2048, 66⟩, ⟨12, 128, 66⟩, 4, 2, 66⟩, ⟨⟨14, 2048, 66⟩, ⟨14, 512, 66⟩, 0, 0, 66⟩]
  work := 32
  salt := 40

/-- **The 24 rounds, written**: by the format's own makers of rounds: the library's list, but for
the round BAT, which batches two rows more, one for each table's record.
-/
def smallRecordFmt : List Fmt.Round :=
  (Fmt.M3.roundsOf smallRecordPar).set 5
    (Fmt.M2.rBatN (2 * smallRecordPar.s + Fmt.M3.nRows smallRecordPar))

/-- **The openings of stored tables, round by round, written**: at the round LINK the first table's
at the first draws and the copy's at the last; elsewhere none. -/
def smallRecordStored : List (List Fmt.Stored) :=
  smallRecordFmt.map fun r =>
    if r.entry.name == "LINK" then
      [⟨Fmt.M3.shT smallRecordPar, smallRecordPar.salt, 0, 0, smallRecordPar.nu0⟩,
        ⟨Fmt.M3.shT smallRecordPar, smallRecordPar.salt, 1, smallRecordPar.nu0, smallRecordPar.nuj⟩]
    else []

/-- **The rounds of an entry's chain, each with the stored trees that it opens, WRITTEN.** No run of
a program stands in this term. -/
def smallRecordRounds : Rounds := smallRecordFmt.zip smallRecordStored

/-- A YARDSTICK: the dry run of the Lean port's link at keys of zeros states just these rounds. -/
theorem small_record_rounds : entryRoundsAny smallRecordRead = some smallRecordRounds := by
  have h : (entryRoundsAny smallRecordRead).get small_record_dry = smallRecordRounds :=
    List.zip_of_prod (rounds_of_parts (by decide +kernel)) (by decide +kernel)
  rw [← h]
  exact (Option.some_get small_record_dry).symm

/- The elaborator is not to unfold the written list:
the files above are written so. Lean's kernel unfolds it where a proof evaluates. -/
attribute [irreducible] smallRecordRounds

/-- The dry run states 24 rounds. -/
theorem small_record_rounds_length : smallRecordRounds.length = 24 := by decide +kernel

/-- These are as many as the chain's rounds as read: the plan's entries but for the entry RECORD. -/
theorem small_record_rounds_all :
    smallRecordRounds.length = smallRecordRead.given.rounds.length := by
  decide +kernel

/-- Under `smallRecordRead` and for all tables, if the rounds of the dry run of a link's block are
the same at all keys of these sizes and items: a description that `Tie.entrySpec` gives is made of
the parameter bytes, these rounds and the statement. Nothing says that it gives one. -/
theorem small_record_entrySpec (H : LinkDryBySizes smallRecordLink) {first further : TableName}
    {block : Blk Unit} {S : Fmt.SpecX}
    (h : Tie.entrySpec smallRecordRead first further = some (block, S)) :
    S = entrySpecOf smallRecordRead smallRecordRounds (Link.statement first further) := by
  obtain ⟨_, r, hr, hS⟩ := entrySpec_eq_any (p := smallRecordRead) H h
  have hrr : smallRecordRounds = r := Option.some.inj (small_record_rounds.symm.trans hr)
  rw [hS, ← hrr]

end OnBytes.Params
