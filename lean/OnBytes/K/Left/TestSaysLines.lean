-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/TestSaysLines.lean: the one test on a parameter file that the theorems of
OnBytes/K/Left/ ask (`EntryGround.SaysLines`, OnBytes/Tie/EntryGround.lean), evaluated at copies of
the first 32 lines of the examples' parameter files. Each test is checked when the file compiles.
The file is no part of the program.

`G.SaysLines pol` says: what `Params.readLines` reads of pol's first 32 lines is G's. It is an
equation between values of a type with decidable equality. `linesAre G pol` is Lean's decision of
it, and `linesAre_iff` says so.

The copies. `full32`: the first 32 lines of prover/examples/target_full_f2/policy.txt (the same file
as examples/full-size/config/policy.txt). `small32`: the first 32 lines of
prover/examples/target_small_f2/policy.txt; target_small_f2_gap (the same file as
examples/accepted-proof-clipped-gap/config/policy.txt) and target_small_f2_roomy (the same file as
examples/accepted-proof/config/policy.txt) have the same 32 lines.
The four files' sha256 sums,
in that order:
  ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae
  3c7ff5cb3b323c6ce23dcb011494d6f94b6f75c8056c7b1e3e3ae6309a1cd50e
  735077ff031e0d679f430c85fc92b3d82177044b045e68574a7f7c0d23f3b2ae
  8d9ae1dda2e503550cafade93c54c1b8ecc8eb4b6dab3b843c72a478bb892d2f
The sha256 sums of the 32 lines, each line with its line feed, as `bytesOf` spells them:
  98ba1ef1a36978d347cb10e89125a8f64297ce68af81e8df1f57255ca08e5484  (full32)
  b21e4564a809f9d0f70a585460cfcb6990d5151b0fe270c1273da5c30a6f0ef5  (small32)
A reader can take them with: head -n 32 policy.txt | sha256sum.

The tests. True: `full32` at the full-size ground, `small32` at the small ground. False: each at the
other ground; `full32` with one digit of line 15 turned, which is read; `small32` with lines 2 and 3
swapped, which the reader refuses; and `small32` with the table's line of
prover/examples/target_small_file_f2/policy.txt, an example that is at neither ground.
`full_says`, `small_says`: the two true ones as theorems, decided by Lean's kernel.

Limits: the tests are at the first 32 lines, not at whole files: that the lines behind them do not
turn what is read of the first 32 is shown in OnBytes/K/Left/SaysLinesPrefix.lean. That the copies
are any file's lines rests on the sums above; nothing in OnBytes/ reads a folder of examples.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryGrounds

set_option autoImplicit false

namespace OnBytes.K.Left.TestSaysLines
open OnBytes.Tie

/-- Lean's decision of the equation that `G.SaysLines pol` is. -/
def linesAre (G : EntryGround) (pol : ByteArray) : Bool :=
  decide ((Params.readLines pol).toOption.map (·.1) = some G.lines)

/-- It decides `G.SaysLines pol`. -/
theorem linesAre_iff (G : EntryGround) (pol : ByteArray) :
    linesAre G pol = true ↔ G.SaysLines pol := by
  unfold linesAre EntryGround.SaysLines
  exact decide_eq_true_iff

/-- Lines as bytes: each line with its line feed. -/
def bytesOf (l : List String) : ByteArray := (String.join (l.map (· ++ "\n"))).toUTF8

/-- The first 32 lines of the full-size example's parameter file. -/
def full32 : List String :=
  ["version H821",
   "sec 128",
   "reading 1",
   "rowcost 1",
   "slots 64",
   "answers 1",
   "record 1",
   "work field 0 0 0",
   "work sample 0 0 0",
   "work closeness 0 0 0",
   "work positions 20 28 32",
   "work smallness 0 0 0",
   "salt 40",
   "listed 0",
   "group link 1 23 22 17 13",
   "stages link 4 3 22 17 3 3 19 16 3 3 16 15 4 4 13 13 0 0 15 15",
   "group folded 1 24 22 13 6",
   "stages folded 5 2 21 12 4 2 17 12 4 2 13 12 0 0 14 14",
   "group omega 1 22 18 13 6",
   "stages omega 4 3 18 14 4 3 14 13 0 0 15 15",
   "group own 1 22 18 13 8",
   "stages own 4 3 18 15 3 3 15 14 3 3 13 13 0 0 15 15",
   "group once-folded 1 24 22 13 6",
   "stages once-folded 5 2 21 12 4 2 17 12 4 2 13 12 0 0 14 14",
   "group once-omega 1 22 18 13 6",
   "stages once-omega 4 3 18 14 4 3 14 13 0 0 15 15",
   "group once-own 1 22 18 13 8",
   "stages once-own 4 3 18 15 3 3 15 14 3 3 13 13 0 0 15 15",
   "group once-ranges 1 22 18 16 12",
   "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20",
   "ranges-part 18",
   "table 11 32 402653184 44040191 0 18"]

/-- The first 32 lines of three small examples' parameter files. -/
def small32 : List String :=
  ["version H821",
   "sec 128",
   "reading 1",
   "rowcost 1",
   "slots 64",
   "answers 1",
   "record 1",
   "work field 0 0 0",
   "work sample 0 0 0",
   "work closeness 0 0 0",
   "work positions 20 28 32",
   "work smallness 0 0 0",
   "salt 40",
   "listed 0",
   "group link 1 18 17 17 13",
   "stages link 4 3 17 17 3 3 16 16 3 3 15 15 0 0 15 15",
   "group folded 1 17 15 13 6",
   "stages folded 4 2 14 12 0 0 14 14",
   "group omega 1 18 14 13 6",
   "stages omega 4 3 14 13 0 0 15 15",
   "group own 1 18 14 13 8",
   "stages own 4 3 14 13 0 0 15 15",
   "group once-folded 1 17 15 13 6",
   "stages once-folded 4 2 14 12 0 0 14 14",
   "group once-omega 1 18 14 13 6",
   "stages once-omega 4 3 14 13 0 0 15 15",
   "group once-own 1 18 14 13 8",
   "stages once-own 4 3 14 13 0 0 15 15",
   "group once-ranges 1 22 18 16 10",
   "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20",
   "ranges-part 14",
   "table 8 23 524288 65535 0 11"]

#guard full32.length == 32 && small32.length == 32
#guard linesAre recordGround (bytesOf full32)
#guard linesAre smallRecordGround (bytesOf small32)
#guard !linesAre smallRecordGround (bytesOf full32)
#guard !linesAre recordGround (bytesOf small32)
-- one digit of line 15 turned: the reader reads it, and the lines are others
#guard full32[14]! == "group link 1 23 22 17 13"
#guard (Params.readLines (bytesOf (full32.set 14 "group link 1 23 22 17 12"))).toOption.isSome
#guard !linesAre recordGround (bytesOf (full32.set 14 "group link 1 23 22 17 12"))
-- lines 2 and 3 swapped: the reader refuses
#guard !linesAre smallRecordGround (bytesOf ((small32.set 1 small32[2]!).set 2 small32[1]!))
-- the table's line of the example target_small_file_f2
#guard !linesAre smallRecordGround (bytesOf (small32.set 31 "table 8 26 7864320 524287 0 14"))
#guard !linesAre recordGround (bytesOf (small32.set 31 "table 8 26 7864320 524287 0 14"))

/-- At the full-size example's lines, by Lean's kernel. -/
theorem full_says : recordGround.SaysLines (bytesOf full32) :=
  (linesAre_iff _ _).1 (by decide +kernel)

/-- At the small examples' lines, by Lean's kernel. -/
theorem small_says : smallRecordGround.SaysLines (bytesOf small32) :=
  (linesAre_iff _ _).1 (by decide +kernel)

end OnBytes.K.Left.TestSaysLines
