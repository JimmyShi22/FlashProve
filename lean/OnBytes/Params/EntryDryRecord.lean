-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryDryRecord.lean: parameter bytes typed for an entry's chain at the full-size
files of the setting "record with work", read; the chain's rounds, written; and a yardstick: the dry
run of the program's link states these rounds.

OnBytes/Params/EntryStagesRecord.lean types a plan, codes and a link's shape, and
OnBytes/Params/EntryParamsRecord.lean proves that they are what `entrySized` returns at
`recordLines`. Here the parameter bytes `recordBytes` are spelled from them and from a typed digest,
`recordCfg`. They are the bytes that `entryParams` returns at `recordLines` and that digest
(`record_bytes`). They are read as those of a link's chain (`record_read`). The typed shape says
that tables have 2 ^ 11 rows and a record of one answer a row (`record_answers`). The rounds of the
chain, each with the stored trees that it opens, are WRITTEN (`recordRounds`): by the format's own
makers of rounds at a typed record of sizes (`recordPar`, `recordFmt`, `recordStored`); no run of a
program stands in that term. There are 41 of them (`record_rounds_length`): as many as the plan has
entries but for the entry RECORD (`record_rounds_all`). A YARDSTICK: the dry run of the link's block
at two keys of zeros of these sizes returns rounds (`record_dry`), and they are the written ones
(`record_rounds`). The block is that of the program; the program is the Lean text `verify-on-bytes`,
not the C++ verifier. With OnBytes/Params/EntryRoundsRecord.lean this gives, for any two
tables, the description that `Tie.entrySpec` gives under these bytes, if it gives one: these
parameter bytes, these rounds, and the link's statement on the two tables; under the hypothesis
`LinkDryBySizes recordLink`, that the dry run's rounds are the same at all keys of these sizes and
items (`record_entrySpec`); OnBytes/Params/EntryDescRecord.lean takes the hypothesis away.


Main definitions: `recordCfg`, `recordItems`, `recordBytes`, `recordRead`, `recordPar`, `recordFmt`,
`recordStored`, `recordRounds`.
Main theorems: `record_bytes`, `record_read`, `record_answers`, `record_dry`, `record_rounds`,
`record_rounds_length`, `record_rounds_all`, `record_entrySpec`.
What is not claimed: that these are the bytes that the C++ verifier hashes. That the digest of any
three public files is `recordCfg`: a test computes that value from copies of three files, and by
that test's head the C++ verifier cp_verify printed it in a planning call on three files, whose
sha256 sums the head names (a test that is not in this library); no print is kept in this tree.
`LinkDryBySizes recordLink`: a hypothesis. That `Tie.entrySpec` gives a description: a test has it
give one at two made-up tables (a test that is not in this library); no theorem. With a record
the block depends on the two tables; nothing is said of it here. Nothing on soundness, on what a
round's price is worth under the rule `johnson`, or on what a round's work is worth. For proofs
only; the program does not import this file.


-/
import OnBytes.Params.EntryRoundsToy
import OnBytes.Params.EntryParamsRecord
import OnBytes.Params.EntryRoundsRecord
import OnBytes.Params.Spell
import OnBytes.Params.ToyDescriptions

set_option autoImplicit false

namespace OnBytes.Params

/-- A digest typed for three full-size public files of the setting. -/
def recordCfg : ByteArray :=
  Fmt.unhex "cf8ebe88802355fc0921fbbd3cc6aa770d01579b5750d1a88ab2d50cd0a5b118"

/-- The two items after the digest. -/
def recordItems : List (String × ByteArray) :=
  [("codes", spellCodes recordCodes), ("the link", spellLink recordLink)]

/-- The parameter bytes that are spelled from the typed plan, digest, codes and shape. -/
def recordBytes : ByteArray := Fmt.paramsBytes recordPlan recordCfg recordItems

/-- What the parameter bytes hold as those of a link's chain. -/
def recordRead : Link :=
  ⟨⟨recordBytes, recordPlan, recordCfg, recordItems⟩, recordCodes, recordLink⟩

/-- At `recordLines` and the typed digest the parameter bytes of an entry's chain are
`recordBytes`. -/
theorem record_bytes : entryParams recordLines recordCfg = .ok recordBytes := by
  obtain ⟨P, hy, hp, _⟩ := record_sized
  unfold entryParams
  rw [hy]
  show (Except.ok (Fmt.paramsBytes P.plan recordCfg recordItems) : Except String ByteArray) = _
  rw [hp]
  rfl

/-- The parameter bytes `recordBytes` are read as those of a link's chain. -/
theorem record_read : Link.read recordBytes = some recordRead :=
  Link.read_of
    (Given.read_spelled recordPlan recordCfg recordItems
      (fit_of (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel))
    rfl (by decide +kernel) (by decide +kernel)

/-- The shape that is typed says that tables have a record of one answer a row, and 2 ^ 11 rows. -/
theorem record_answers : recordRead.link.table.answers = 1 ∧ recordRead.link.table.rows = 2048 := by
  decide +kernel

/-- Under `recordRead` the dry run of the link's block, the program's, at keys of zeros returns
rounds. -/
theorem record_dry : (entryRoundsAny recordRead).isSome = true := by decide +kernel

/-- The format's record of sizes at these files, typed. -/
def recordPar : Fmt.M3.Par where
  fld := .two
  T := ⟨32, 402653184, 44040191⟩
  v := 11
  s := 1
  nu0 := 62
  nuj := 62
  C := ⟨24, 4194304, 97⟩
  Z := ⟨13, 64, 97⟩
  R := 107
  stages := [⟨⟨24, 4194304, 97⟩, ⟨13, 64, 97⟩, 8, 0, 97⟩,
    ⟨⟨21, 131072, 49⟩, ⟨12, 128, 49⟩, 5, 2, 49⟩,
    ⟨⟨17, 8192, 49⟩, ⟨12, 128, 49⟩, 4, 2, 49⟩,
    ⟨⟨13, 512, 50⟩, ⟨12, 128, 50⟩, 4, 2, 50⟩,
    ⟨⟨14, 512, 40⟩, ⟨14, 512, 40⟩, 0, 0, 40⟩]
  work := 32
  salt := 40

/-- **The 41 rounds, written**: by the format's own makers of rounds: the library's list, but for
the round BAT, which batches two rows more, one for each table's record.
-/
def recordFmt : List Fmt.Round :=
  (Fmt.M3.roundsOf recordPar).set 5 (Fmt.M2.rBatN (2 * recordPar.s + Fmt.M3.nRows recordPar))

/-- **The openings of stored tables, round by round, written**: at the round LINK the first table's
at the first draws and the copy's at the last; elsewhere none. -/
def recordStored : List (List Fmt.Stored) :=
  recordFmt.map fun r =>
    if r.entry.name == "LINK" then
      [⟨Fmt.M3.shT recordPar, recordPar.salt, 0, 0, recordPar.nu0⟩,
        ⟨Fmt.M3.shT recordPar, recordPar.salt, 1, recordPar.nu0, recordPar.nuj⟩]
    else []

/-- **The rounds of an entry's chain, each with the stored trees that it opens, WRITTEN.** No run of
a program stands in this term. -/
def recordRounds : Rounds := recordFmt.zip recordStored

/-- A YARDSTICK: the dry run of the program's link at keys of zeros states just these rounds. -/
theorem record_rounds : entryRoundsAny recordRead = some recordRounds := by
  have h : (entryRoundsAny recordRead).get record_dry = recordRounds :=
    List.zip_of_prod (rounds_of_parts (by decide +kernel)) (by decide +kernel)
  rw [← h]
  exact (Option.some_get record_dry).symm

/- The elaborator is not to unfold the written list: the files above are written so. Lean's kernel
unfolds it where a proof evaluates. -/
attribute [irreducible] recordRounds

/-- The dry run states 41 rounds. -/
theorem record_rounds_length : recordRounds.length = 41 := by decide +kernel

/-- These are as many as the chain's rounds as read: the plan's entries but for the entry RECORD. -/
theorem record_rounds_all : recordRounds.length = recordRead.given.rounds.length := by
  decide +kernel

/-- Under `recordRead` and for all tables, if the rounds of the dry run of a link's block are the
same at all keys of these sizes and items: a description that `Tie.entrySpec` gives is made of the
parameter bytes, these rounds and the statement. Nothing says that it gives one. -/
theorem record_entrySpec (H : LinkDryBySizes recordLink) {first further : TableName}
    {block : Blk Unit} {S : Fmt.SpecX}
    (h : Tie.entrySpec recordRead first further = some (block, S)) :
    S = entrySpecOf recordRead recordRounds (Link.statement first further) := by
  obtain ⟨_, r, hr, hS⟩ := entrySpec_eq_any (p := recordRead) H h
  have hrr : recordRounds = r := Option.some.inj (record_rounds.symm.trans hr)
  rw [hS, ← hrr]

end OnBytes.Params
