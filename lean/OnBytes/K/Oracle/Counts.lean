-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/Counts.lean: how many strings the typing of an entry file asks at most, as numbers,
at the two grounds with a record.

`Tie.typedT s r0` (OnBytes/Tie/EntryAskedCost.lean) is a closed expression of the tables' shape and
the rounds: it bounds the strings that `Tie.typedER asm q first ent` asks (the reading of the entry
file that asks, both tables' seeds once more, then any plain map asm). The full size's number is
evaluated there (`Tie.record_typedT`); the small size's here.

Main names:
  `small_typedT`: at the small size the expression is 26222.
  `record_count`, `small_record_count`: the two numbers at the grounds' own shape and rounds.

What is not claimed. The numbers are upper bounds: every call of the hash counts as two strings, a
repeated string counts again, and nothing says that a bound is attained. Nothing on which strings
are asked. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Params.EntryDryRecordSmall
import OnBytes.Tie.EntryAskedCost
import OnBytes.Tie.EntryGrounds
import OnBytes.Tie.EntryRecord

set_option autoImplicit false

namespace OnBytes.K.Oracle
open OnBytes.Tie (recordGround smallRecordGround typedT)

/-- At the small size: 26,028 for the reading and 2 · 97 for the seeds once more. -/
theorem small_typedT :
    typedT Params.smallRecordRead.link.table Params.smallRecordRounds = 26222 := by
  decide +kernel

/-- The full size's number, at the ground's own shape and rounds. -/
theorem record_count : typedT recordGround.q.link.table recordGround.rs = 41622 :=
  OnBytes.Tie.record_typedT

/-- The small size's number, at the ground's own shape and rounds. -/
theorem small_record_count : typedT smallRecordGround.q.link.table smallRecordGround.rs = 26222 :=
  small_typedT

end OnBytes.K.Oracle
