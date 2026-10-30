-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Tape/RowsOwed.lean: the count of batched rows that the round closed last still
owes, as plain data. Definitions with code. No theorem. It imports nothing.

Why. Some entries of a plan count batched rows: the error that the plan books for such a round rests
on that number. The program's channel keeps two fields for it, the entry of the round closed last
and whether its count has been compared (`Chan.last`, `Chan.askedRows`:
OnBytes/Iop/Ground.lean:587-590), and three places read or write them: a close lays them (:844) and
refuses while a count waits (`Chan.settled`, :602-605, asked at :825); `Blk.requireRows` compares
(:851-857); the run's end asks `settled` once more (:958, :981). The draw and the comparison often
stand in two different steps of a chain's decision, so what waits must be carried between them. Here
it is one value with four functions, for every step that is a plain function on data.

Main names:
  `RowsOwed`: `some r`: the round closed last counts r rows, and nobody has compared that number;
    `none`: no round has been closed, or the count has been compared.
  `RowsOwed.set rows`: **behind a close**, rows the closed entry's count, 0 too.
  `RowsOwed.noneWaits`: **no count waits**: what a close, and a run's end, ask first.
  `RowsOwed.compare o rows`: **the comparison**: what is owed behind it, or nothing.
  `RowsOwed.close o rows`: noneWaits and set in one, so that the first cannot be forgotten.

Limits: it is the program's on a view; its dry run compares nothing (:854). ONE PARTING FROM THE
PROGRAM, ON THE REFUSING SIDE: a SECOND comparison behind one close. The program keeps the entry, so
it passes the same number again; here the count is gone once compared, and `compare none _` refuses.
To pass it the value would have to hold the number and the mark both. By a reading of the program's
text it costs no honest run: its routines compare in six places, each once, behind the close whose
entry it asks (OnBytes/Iop/Bat.lean:66, :79; Cs.lean:613; Batt.lean:107;
OnBytes/Model/Rounds.lean:180, called at Trees.lean:450 and, right behind its own close, in
`trBatch`, Rounds.lean:190, which the links' routines call as `SubM.batch`, Hide.lean:482); a toy
has one more (OnBytes/Proof/ToyLinks.lean:69). `none` stands for two states of the program (no round
closed yet; compared): they differ in that second comparison alone. `set 0` IS `some 0`, NOT `none`:
A CALLER ASKS `noneWaits`, NEVER `isNone` OR THE PATTERN `none`. That `set` is handed the count of
the entry that was in fact closed, and that every close asks `noneWaits`, is the caller's. Nothing
has been shown of it.

THE GUARDS. A row: the program's file:line · where it stands here · class (P: a turned plan can trip
it; T: no input can).
  Ground.lean:604 the entry counts no rows, or they have been compared · noneWaits · P
  Ground.lean:605 no round has been closed: nothing waits · noneWaits, first arm · T
  Ground.lean:825 (third clause) a close while a count waits · close · P
  Ground.lean:854 the number is the entry's · compare, first arm · P
  Ground.lean:857 a comparison where no round has been closed · compare, second arm · T

Terms: lean/GLOSSARY.md.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Tape

/-- The count of batched rows that the round closed last still owes. -/
abbrev RowsOwed : Type := Option Nat

namespace RowsOwed

/-- Behind a close. rows: what the closed round's entry counts. -/
def set (rows : Nat) : RowsOwed := some rows

/-- No count waits. -/
def noneWaits : RowsOwed → Bool
  | none => true
  | some r => r == 0

/-- The comparison of a step's own number of rows with the count that waits. -/
def compare : RowsOwed → Nat → Option RowsOwed
  | some r, rows => if r == rows then some none else none
  | none, _ => none

/-- A close: refused while a count waits; else the closed entry's count is laid. -/
def close (o : RowsOwed) (rows : Nat) : Option RowsOwed :=
  if noneWaits o then some (set rows) else none

end RowsOwed

end VerifiableInference.Desc.First.Tape
