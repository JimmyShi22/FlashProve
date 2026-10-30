-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RecordFull.lean: the data of OnBytes/Slice/RecordRead.lean at
the sizes of the full-size parameter file with a record. DEFINITIONS AND SIX FACTS ON NUMBERS BY
EVALUATION.




WHICH FILE. The 32 lines of the example file record.f2.txt, which OnBytes/Params/TestExamples.lean
holds as text (`record`); a parameter file's first 32 lines are read by OnBytes/Params/File.lean.
Used here: line 6 "answers 1"; line 7 "record 1"; line 13 "salt 40"; line 32 "table 11 32 402653184
44040191 0 18", whose six numbers are: the logarithm of the number of rows; the logarithm of the
word's length; the entries of a row's message; the entries of the random tail; the radius, which
must be 0 exactly if tables have a record; a number of the blocks that is not used here. NOT USED:
line 11 "work positions 20 28 32" and every other line: no word on work, distances or errors stands
in this file.

Main definitions.
 `recT`, `recV`, `recS`, `recLg`, `recShape`   the sizes, each with its line.
 `decRecFull eM`   `decRec` there: a closed term but for the radius.

Main theorems.
 `recShape_sizes`, `recShape_cubeBits`, `recShape_ok`, `recShape_plain`   the shape's numbers are
                        the sizes; 29 coordinates; the shape passes the programs' test; 402653181
                        entries before the pads.
 `recT_room`, `rec_questions`   the two conditions of `recZ_okOn`; 71 calls, 143
                        questions for a table's seeds.



What is not claimed. eM, THE RADIUS IN COLUMNS, IS AN ARGUMENT: the file names none, and the
planner's derived distances are not read here. That these are the sizes of any file that a program
is run with: the numbers were copied by hand from these lines, and no theorem ties them to that text
or to the reader of OnBytes/Params/File.lean. (OnBytes/Slice/RecordPriceGlue.lean ties them to what
the planner derives at the typed lines `recordLines`: `recordTable_sizes`, `recordLink_recShape`.)
No part for a key, an entry or a proof at these sizes is written.


-/
import OnBytes.Slice.WrapLaw

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal
open OnBytes.Tie (IdKey idCode firstId)

/-! ## The sizes -/

/-- The code of a row of the stored tables. Line 32, "table 11 32 402653184 44040191 0 18": its
second number is the logarithm of the word's length, its third the entries of a row's message (the
pads counted in), its fourth the entries of the random tail. -/
def recT : Fmt.M1.Code := ⟨32, 402653184, 44040191⟩

/-- The number of row variables: a table has 2^11 rows. Line 32, first number. -/
def recV : ℕ := 11

/-- The answers for each row. Line 6, "answers 1"; line 7, "record 1", says that tables have a
record. -/
def recS : ℕ := 1

/-- The coordinates of a seed's point: the least lg with 402653184 ≤ 2^lg (`IndexShape.cubeBits`).
In no line; it follows from line 32's third number. -/
def recLg : ℕ := 29

/-- The tables' shape, as the programs have it. The bytes of a leaf's salt: line 13, "salt 40". -/
def recShape : Params.IndexShape := ⟨⟨32, 402653184, 44040191⟩, 11, 1, 40⟩

/-- The shape's numbers are the sizes above. -/
theorem recShape_sizes : recShape.code.logN = recT.a ∧ recShape.code.ell = recT.l ∧
    recShape.code.r = recT.r ∧ recShape.v = recV ∧ recShape.answers = recS :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `recLg` is the number of coordinates that the programs take at that shape. -/
theorem recShape_cubeBits : recShape.cubeBits = recLg := by decide

/-- That shape passes the programs' test on a table's shape. -/
theorem recShape_ok : recShape.ok = true := by decide

/-- The entries of a row's message before its pads. -/
theorem recShape_plain : recShape.plain = recT.l - 3 * recS := by decide

/-- The message has room for its pads, and its entries before the pads are at most 2^29. -/
theorem recT_room : 3 * recS ≤ recT.l ∧ recT.l - 3 * recS ≤ 2 ^ recLg := by decide

/-- The calls number 162 in the seeds' round, and the questions for a table's seeds. -/
theorem rec_questions : seedCalls recLg recS = 71 ∧ 2 * seedCalls recLg recS + 1 = 143 := by decide

/-! ## The decoder's data -/

/-- **The data of a decoder at these sizes.** eM, THE RADIUS IN COLUMNS, IS AN ARGUMENT: the
parameter file names none: with "record 1" the fifth number of line 32 must be 0
(OnBytes/Params/File.lean), and the planner derives the two distances of a table with a record, up
to the Johnson radius, as integers of its own (OnBytes/Params/Group.lean). -/
@[reducible] noncomputable def decRecFull (eM : ℕ) : DecR := decRec recT recV eM recLg recS

end OnBytes.Slice
