-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestConfigOrder.lean: further tests of the strict scan of OnBytes/Model/Config.lean,
which run when this file is compiled.

OnBytes/Model/TestConfig.lean tries one case for most of the refusals that have a name of their own,
and for a few of the names that come from the frame's reader or end in a line's number or name. This
file goes through some clauses one by one: for each optional line every line that must not come
before it, the bounds of each optional line's value from both sides, the three tests on the frame's
lines number by number, and faults in the lines prof, lt and toksrc, which are read before the scan.
The files are altered copies of the example's parameter file, which TestConfig.lean spells out.

What this file does not claim. The expected names were read off the C++ source, clause by clause
(verifier/src/cp_verify.cpp: polWord, polPrescan, polScan, and the two tests on lt that follow
polPrescan in runStage). No C++ program was run on these files. No program imports this file.
-/
import OnBytes.Model.TestConfig

namespace OnBytes.Model.TestConfigOrder

open OnBytes.Model.TestConfig

/-- The 32 lines of the tables' digests. -/
def tableLines : List String := optionalLines.drop 4

/-- The name under which the scan refuses the example's file with these optional lines. -/
def withOptional (o : List String) : Option String := refusal (withLines valueLines o callLines)

/-- The name under which the scan refuses the example's file with these optional lines and one more
line after the call lines. -/
def afterCalls (o : List String) (x : String) : Option String :=
  refusal (withLines valueLines o (callLines ++ [x]))

/-- True if the line x is refused under the name after each of the lists of optional lines, each of
which the scan admits by itself. -/
def refusedAfter (x name : String) (before : List (List String)) : Bool :=
  before.all fun o => withOptional o == none && withOptional (o ++ [x]) == some name

/-- The example's frame with another line in the place of the line that begins with head. -/
def frameWith (head line : String) : List String :=
  frameLines.map fun l => if l.startsWith head then line else l

/-- The name under which the scan refuses the value lines under another frame. -/
def underFrame (head line : String) : Option String :=
  refusal (fileOf (frameWith head line ++ valueLines))

/-! ## The order of the optional lines -/

-- all of them, in their order
#guard withOptional (["lidb 24", "nminH 21", "eg 4", "smax 511", "rcl 1", "gcl 1", "xl 5"] ++
  tableLines) == none
#guard tableLines.length == 32

#guard refusedAfter "lidb 24" "policy-lidb" [["lidb 24"], ["lidb 24", "nminH 21"], ["eg 4"],
  ["smax 511"], ["rcl 1"], ["gcl 1"], ["xl 5"], tableLines]
#guard afterCalls [] "lidb 24" == some "policy-lidb"
#guard withOptional ["nminH 21"] == some "policy-nminH"
#guard refusedAfter "nminH 21" "policy-nminH" [["lidb 24", "nminH 21"], ["lidb 24", "eg 4"],
  ["lidb 24", "smax 511"], ["lidb 24", "rcl 1"], ["lidb 24", "gcl 1"], ["lidb 24", "xl 5"],
  "lidb 24" :: tableLines]
#guard afterCalls ["lidb 24"] "nminH 21" == some "policy-nminH"
#guard refusedAfter "eg 4" "policy-gate-table" [["eg 4"], ["smax 511"], ["rcl 1"], ["gcl 1"],
  ["xl 5"], tableLines]
#guard afterCalls [] "eg 4" == some "policy-gate-table"
#guard refusedAfter "smax 511" "policy-gate-table" [["smax 511"], ["rcl 1"], ["gcl 1"], ["xl 5"],
  tableLines]
#guard afterCalls [] "smax 511" == some "policy-gate-table"
#guard refusedAfter "rcl 1" "policy-rcl" [["rcl 1"], ["gcl 1"], ["xl 5"], tableLines]
#guard afterCalls [] "rcl 1" == some "policy-rcl"
#guard refusedAfter "gcl 1" "policy-gcl" [["gcl 1"], ["xl 5"], tableLines]
#guard afterCalls [] "gcl 1" == some "policy-gcl"
#guard refusedAfter "xl 5" "policy-xl" [["xl 5"], tableLines]
#guard afterCalls [] "xl 5" == some "policy-xl"

/-! ## The values of the optional lines -/

#guard withOptional ["lidb 23"] == none && withOptional ["lidb 30"] == none
#guard withOptional ["lidb 22"] == some "policy-lidb"
#guard withOptional ["lidb 31"] == some "plan-identity-cap"
#guard withOptional ["lidb x"] == some "policy-lidb"
#guard withOptional ["lidb 24", "nminH 2"] == none && withOptional ["lidb 24", "nminH 28"] == none
#guard withOptional ["lidb 24", "nminH 1"] == some "policy-nminH"
#guard withOptional ["lidb 24", "nminH 29"] == some "policy-nminH"
#guard ["eg 4", "eg 5", "eg 6", "eg 7"].all fun x => withOptional [x] == none
#guard ["eg 3", "eg 8"].all fun x => withOptional [x] == some "policy-gate-table"
#guard ["smax 2047", "smax 1023", "smax 511", "smax 255"].all fun x => withOptional [x] == none
#guard ["smax 4095", "smax 2048", "smax 256", "smax 254", "smax 0"].all fun x =>
  withOptional [x] == some "policy-gate-table"
#guard ["rcl 0", "rcl 2"].all fun x => withOptional [x] == some "policy-rcl"
#guard ["gcl 0", "gcl 2"].all fun x => withOptional [x] == some "policy-gcl"
#guard ["xl 4", "xl 6"].all fun x => withOptional [x] == some "policy-xl"

/-! ## The lines of the tables' digests -/

-- all 32 after the call lines; eight, the call lines, and the other 24
#guard refusal (withLines valueLines [] (callLines ++ tableLines)) == some "policy-tables"
#guard refusal (withLines valueLines (tableLines.take 8) (callLines ++ tableLines.drop 8)) ==
  some "policy-tables"
-- two lines swapped; the tables in another order
#guard withOptional (tableLines[1]! :: tableLines[0]! :: tableLines.drop 2) == some "policy-tables"
#guard withOptional (tableLines.drop 8 ++ tableLines.take 8) == some "policy-tables"
-- a 33rd line
#guard withOptional (tableLines ++ ["tsilu0 1"]) == some "policy-tables"
-- a 33rd line that is also misspelled (a leading zero; two spaces; twenty digits): its place is
-- tested before its spelling. The two guards after it: a number of 33 bits; the largest of 32 bits
#guard ["tsilu0 01", "tsilu0  1", "tsilu0 12345678901234567890"].all fun x =>
  withOptional (tableLines ++ [x]) == some "policy-tables"
#guard withOptional ("tsilu0 4294967296" :: tableLines.drop 1) == some "policy-tables"
#guard withOptional ("tsilu0 4294967295" :: tableLines.drop 1) == none

/-! ## The three tests on the frame's lines -/

-- each of the table's three numbers has at most 32 bits. The frame's reader
-- (OnBytes/Params/File.lean) admits a code of at most 2 ^ 32 positions and asks that a row's
-- coordinates together, and the radius, be below the code's length. So in every file that it
-- reads the three numbers are below 2 ^ 32, and no file fails the scan's own test. First guard: a
-- line with a number of 33 bits is refused by the reader, under the same name. Second guard: the
-- largest sum of coordinates and the largest radius that the reader admits. Third guard: the
-- scan's own test, tried on values of Params.Lines that no file gives. Fourth guard: that test
-- comes before the test on the work
#guard ["table 8 32 4294967296 65535 0 11", "table 8 32 65535 4294967296 0 11"].all fun l =>
  (Params.readLines (fileOf (frameWith "table " l ++ valueLines))).toOption.isNone &&
    underFrame "table " l == some "parameter-table-shape (policy)"
#guard underFrame "table " "table 8 32 4294967294 1 0 11" == none
#guard (Params.readLines (fileOf (frameLines ++ valueLines))).toOption.any fun x =>
  (frameWords { x.1 with tableData := 2 ^ 32 - 1, tableRandom := 2 ^ 32 - 1 }).toOption.isSome &&
  [{ x.1 with tableData := 2 ^ 32 }, { x.1 with tableRandom := 2 ^ 32 }].all fun f =>
    match frameWords f with
    | .error e => e == "parameter-table-shape (policy)"
    | .ok _ => false
#guard (Params.readLines (fileOf (frameLines ++ valueLines))).toOption.any fun x =>
  match frameWords { x.1 with tableData := 2 ^ 32, workField := ⟨33, 0, 0⟩ } with
  | .error e => e == "parameter-table-shape (policy)"
  | .ok _ => false
-- each of the fifteen numbers of work is at most 32
#guard ["field", "sample", "closeness", "positions", "smallness"].all fun k =>
  underFrame ("work " ++ k) ("work " ++ k ++ " 32 32 32") == none &&
  ["33 0 0", "0 33 0", "0 0 33"].all fun w =>
    underFrame ("work " ++ k) ("work " ++ k ++ " " ++ w) == some "policy-work-most"
-- at most 256 requests in a batch
#guard underFrame "slots " "slots 256" == none
#guard underFrame "slots " "slots 512" == some "policy-leafd"

/-! ## The lines that are read before the scan -/

#guard ["prof 2x", "prof x", "prof 00000000020"].all fun x =>
  refusal (withLines (setLine valueLines 0 x) [] callLines) == some "statement-required"
#guard ["lt 6x", "lt 00000000006"].all fun x =>
  refusal (withLines (setLine valueLines 1 x) [] callLines) == some "policy-name-lt"
#guard ["lt 3", "lt 17"].all fun x =>
  refusal (withLines (setLine valueLines 1 x) [] callLines) == some "shape-words"
#guard ["lt 4", "lt 16"].all fun x =>
  refusal (withLines (setLine valueLines 1 x) [] callLines) == none
#guard ["toksrc 0", "toksrc 2", "toksrc x", "toksrc 00000000001"].all fun x =>
  refusal (withLines (valueLines.map fun l => if l == "toksrc 1" then x else l) [] callLines) ==
    some "statement-required"
-- prof is 16 to 31
#guard ["prof 15", "prof 32"].all fun x =>
  refusal (withLines (setLine valueLines 0 x) [] callLines) == some "statement-required"

end OnBytes.Model.TestConfigOrder
