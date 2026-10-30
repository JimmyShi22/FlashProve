-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypeTest.lean: does the typing of a whole file return? A test that can be evaluated.

`typeFile` (OnBytes/Maker/TypeFile.lean) returns a proof string of a protocol whose shape is data.
Whether it returns hangs on six parts alone, none of which takes the shape as an argument: the
tables of the openings, the stored table's openings, the first chain's run's value, and the typed
plain parts of the three stretches. This file lays the six together as one test.

Main definition. `typeReturns`: all six return. Definitions alone; the law that it is
`(typeFile ..).isSome` is in OnBytes/Maker/TypeTestLaws.lean.


-/
import OnBytes.Maker.TypingT
import OnBytes.Maker.Tables
import OnBytes.Maker.WholeOf

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ

/-- All parts of the typing of a whole file return. -/
def typeReturns (C : CK) (a : ℕ) (W : Three.Whole) (saltBytes : ℕ) (cfg : ByteArray)
    (r : Proof.TailRead) : Bool :=
  (tabsWFull W saltBytes r).isSome && (extWFull a cfg W r).isSome && r.first.out.run.isSome &&
    (plainsT C (WholeD.of a W).ds₁ r.first.out.rounds.toList.dropLast).isSome &&
    (plainsT C (WholeD.of a W).ds₂ r.shared.out.rounds.toList).isSome &&
    (plainsT C (WholeD.of a W).ds₃ r.second.out.rounds.toList).isSome

end OnBytes.Maker
