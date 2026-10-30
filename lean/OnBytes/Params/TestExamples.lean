-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestExamples.lean: the derivation of an entry's sizes at a parameter file.

The file is record.f2.txt of blocks/frame/examples. The numbers that are expected were taken from
the prints of the C++ planning program (blocks/frame/cp_frame.cpp, `-plan leaf`) on this file. Each test is checked when the file
compiles. The file is no part of the program.
-/
import OnBytes.Params.Derive
import OnBytes.Params.TestFile

namespace OnBytes.Params.TestExamples

/-- The lines of record.f2.txt. -/
def record : List String :=
  ["version H821", "sec 128", "reading 1", "rowcost 1", "slots 64", "answers 1", "record 1",
   "work field 0 0 0", "work sample 0 0 0", "work closeness 0 0 0", "work positions 20 28 32",
   "work smallness 0 0 0", "salt 40", "listed 0",
   "group link 1 23 22 17 13", "stages link 4 3 22 17 3 3 19 16 3 3 16 15 4 4 13 13 0 0 15 15",
   "group folded 1 24 22 13 6", "stages folded 5 2 21 12 4 2 17 12 4 2 13 12 0 0 14 14",
   "group omega 1 22 18 13 6", "stages omega 4 3 18 14 4 3 14 13 0 0 15 15",
   "group own 1 22 18 13 8", "stages own 4 3 18 15 3 3 15 14 3 3 13 13 0 0 15 15",
   "group once-folded 1 24 22 13 6", "stages once-folded 5 2 21 12 4 2 17 12 4 2 13 12 0 0 14 14",
   "group once-omega 1 22 18 13 6", "stages once-omega 4 3 18 14 4 3 14 13 0 0 15 15",
   "group once-own 1 22 18 13 8", "stages once-own 4 3 18 15 3 3 15 14 3 3 13 13 0 0 15 15",
   "group once-ranges 1 22 18 16 12", "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20",
   "ranges-part 18", "table 11 32 402653184 44040191 0 18"]

/-- What the planning program prints of an entry: the columns of the first and of the further
table; the integer of the first group's distance; for each stage the entries of a main message,
of a mask message, the random entries and the positions; the number of the plan's entries; and
whether some round holds only with its work. -/
def entryOf (l : List String) :
    Option (Nat × Nat × Nat × List (Nat × Nat × Nat × Nat) × Nat × Bool) :=
  (readLines (TestFile.fileOf l)).toOption.bind fun x =>
    (entrySized x.1).toOption.map fun y =>
      (y.1.shape.columnsFirst, y.1.shape.columnsFurther, y.1.linked.group.m,
       y.1.linked.stages.map (fun s => (s.g.main.ell, s.g.mask.ell, s.g.main.r, s.t)),
       y.2.2.rounds.length, y.2.2.needsWork)

/-- The stages under the Johnson rule. -/
def johnsonStages : List (Nat × Nat × Nat × Nat) :=
  [(4194304, 64, 97, 97), (131072, 128, 49, 49), (8192, 128, 49, 49), (512, 128, 50, 50),
   (512, 512, 40, 40)]

#guard entryOf record == some (62, 62, 182, johnsonStages, 42, true)

end OnBytes.Params.TestExamples
