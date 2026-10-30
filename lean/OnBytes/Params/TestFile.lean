-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestFile.lean: tests of the reader of the parameter file's first 32 lines.

The text is the head of the parameter file of prover/examples/target_small_f2_roomy. Each test is
checked when the file compiles. The file is no part of
the program. The names that are expected of the refusals were read off the text of the C++ reader
(blocks/frame/parameters.h); they were not taken from a run of it.
-/
import OnBytes.Params.File
import OnBytes.Params.Names
import OnBytes.Params.RefusalNames

namespace OnBytes.Params.TestFile

/-- The 32 lines of the small example. -/
def small : List String :=
  ["version H821", "sec 128", "reading 1", "rowcost 1", "slots 64", "answers 1", "record 1",
   "work field 0 0 0", "work sample 0 0 0", "work closeness 0 0 0", "work positions 20 28 32",
   "work smallness 0 0 0", "salt 40", "listed 0", "group link 1 18 17 17 13",
   "stages link 4 3 17 17 3 3 16 16 3 3 15 15 0 0 15 15", "group folded 1 17 15 13 6",
   "stages folded 4 2 14 12 0 0 14 14", "group omega 1 18 14 13 6",
   "stages omega 4 3 14 13 0 0 15 15", "group own 1 18 14 13 8",
   "stages own 4 3 14 13 0 0 15 15", "group once-folded 1 17 15 13 6",
   "stages once-folded 4 2 14 12 0 0 14 14", "group once-omega 1 18 14 13 6",
   "stages once-omega 4 3 14 13 0 0 15 15", "group once-own 1 18 14 13 8",
   "stages once-own 4 3 14 13 0 0 15 15", "group once-ranges 1 22 18 16 10",
   "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20", "ranges-part 14",
   "table 8 23 524288 65535 0 11"]

/-- Lines as the bytes of a file: each line ends with a line feed. -/
def fileOf (l : List String) : ByteArray := (String.join (l.map (· ++ "\n"))).toUTF8

/-- What the lines of the small example say. -/
def smallLines : Option Lines := (readLines (fileOf small)).toOption.map (·.1)

/-- The digest of the small example's three public files (policy.txt, layout.txt, KL.bin), as the
C++ verifier computed it in a run on them. -/
def smallCfg : ByteArray :=
  Fmt.unhex "ee76db0af2ce5af0a9b9d27398aac0adfafc2c5a4c2fb5643bb6a9bcb2535a56"

/-- The name under which a file is refused, or nothing if it is read. -/
def why (l : List String) : Option String :=
  match readLines (fileOf l) with
  | .ok _ => none
  | .error e => some e

/-- The lines with s in the place of line number i, counted from 0. -/
def withLine (i : Nat) (s : String) : List String := small.set i s

-- the file is read; some of its numbers; nothing is left after the last line
#guard why small == none
#guard (readLines (fileOf small)).toOption.any fun x =>
  x.1.sec == 128 && x.1.slots == 64 && x.1.link == (⟨18, 17, 17, 13,
    [⟨4, 3, 17, 17⟩, ⟨3, 3, 16, 16⟩, ⟨3, 3, 15, 15⟩, ⟨0, 0, 15, 15⟩]⟩ :
      GroupLine) &&
  x.1.onceRanges.stages.length == 3 && x.1.rangesPart == 14 && x.1.tableRowsLog == 8 &&
  x.1.tableLogN == 23 && x.1.tableData == 524288 && x.1.tableRandom == 65535 &&
  x.1.blockLog == 11 && x.2.size == 0
-- what follows the line table is handed on
#guard (readLines (fileOf (small ++ ["prof 20"]))).toOption.any fun x => x.2 == "prof 20\n".toUTF8
-- lines: one is missing; the last has no line feed; another order; blanks; numbers of values
#guard why (small.take 31) == some "parameter-line-missing: table"
#guard (match readLines ((fileOf small).extract 0 ((fileOf small).size - 1)) with
  | .error e => e == "parameter-line-missing: table"
  | .ok _ => false)
#guard why (withLine 1 "reading 1") == some "parameter-line-order: sec"
#guard why ("" :: small) == some "parameter-line-order: version"
#guard why (withLine 1 "sec  128") == some "parameter-line-blanks: sec"
#guard why (withLine 1 "sec 128 ") == some "parameter-line-blanks: sec"
#guard why (withLine 1 "sec 128 1") == some "parameter-line-values: sec"
#guard why (withLine 7 "work field 0 0") == some "parameter-line-values: work field"
-- numbers: a leading zero, a sign, a carriage return, sixteen digits
#guard why (withLine 1 "sec 0128") == some "parameter-number-spelling"
#guard why (withLine 1 "sec +128") == some "parameter-number-spelling"
#guard why (withLine 1 "sec 128\r") == some "parameter-number-spelling"
#guard why (withLine 4 "slots 1000000000000000") == some "parameter-number-spelling"
-- the version
#guard why (withLine 0 "version H811") == some "version-of-another-field"
#guard why (withLine 0 "version H822") == some "version-of-another-hash"
#guard why (withLine 0 "version H721") == some "version-of-an-earlier-format"
#guard why (withLine 0 "version HG06") == some "version-of-an-earlier-format"
#guard why (withLine 0 "version H921") == some "version-unknown"
#guard why (withLine 0 "version H8211") == some "version-unknown"
-- ranges
#guard why (withLine 1 "sec 257") == some "parameter-range: sec"
#guard why (withLine 4 "slots 48") == some "parameter-range: slots"
#guard why (withLine 10 "work positions 0 59 0") == some "parameter-range: work positions"
#guard why (withLine 12 "salt 44") == some "parameter-range: salt"
#guard why (withLine 13 "listed 9") == some "parameter-range: listed"
-- every line with a range, just outside it (the bounds are those of blocks/frame/parameters.h)
#guard why (withLine 1 "sec 0") == some "parameter-range: sec"
#guard why (withLine 2 "reading 0") == some "parameter-range: reading"
#guard why (withLine 2 "reading 3") == some "parameter-range: reading"
#guard why (withLine 3 "rowcost 0") == some "parameter-range: rowcost"
#guard why (withLine 3 "rowcost 3") == some "parameter-range: rowcost"
#guard why (withLine 4 "slots 0") == some "parameter-range: slots"
#guard why (withLine 4 "slots 2097152") == some "parameter-range: slots"
#guard why (withLine 5 "answers 0") == some "parameter-range: answers"
#guard why (withLine 5 "answers 5") == some "parameter-range: answers"
#guard why (withLine 6 "record 2") == some "parameter-range: record"
#guard why (withLine 6 "record 0") == some "parameter-range: record"
#guard why (withLine 7 "work field 59 0 0") == some "parameter-range: work field"
#guard why (withLine 8 "work sample 0 0 59") == some "parameter-range: work sample"
#guard why (withLine 9 "work closeness 0 59 0") == some "parameter-range: work closeness"
#guard why (withLine 11 "work smallness 59 0 0") == some "parameter-range: work smallness"
#guard why ((withLine 1 "sec 20").set 7 "work field 20 0 0") == some "parameter-range: work field"
#guard why (((withLine 1 "sec 20").set 7 "work field 19 0 0").set 10 "work positions 0 0 0") == none
#guard why (withLine 1 "sec 32") == some "parameter-range: work positions"
#guard why (withLine 12 "salt 32") == some "parameter-range: salt"
#guard why (withLine 12 "salt 72") == some "parameter-range: salt"
#guard why (withLine 30 "ranges-part 0") == some "parameter-range: ranges-part"
#guard why (withLine 30 "ranges-part 41") == some "parameter-range: ranges-part"
-- just inside
#guard why (withLine 1 "sec 256") == none && why (withLine 4 "slots 1048576") == none &&
  why (withLine 5 "answers 4") == none && why (withLine 12 "salt 64") == none &&
  why (withLine 13 "listed 8") == none && why (withLine 30 "ranges-part 40") == none &&
  why (withLine 10 "work positions 58 58 58") == none
-- the line ranges-part is tested before what several lines show together
#guard why ((withLine 20 "group own 1 18 13 13 8").set 30 "ranges-part 41") ==
  some "parameter-range: ranges-part"
-- a group other than the first
#guard why (withLine 28 "group once-ranges 3 22 18 16 10") ==
  some "parameter-group-shape: once-ranges"
#guard why (withLine 23 "stages once-folded 4 2 15") == some "parameter-stages-count: once-folded"
#guard why (withLine 19 "stages omega 4 5 14 13 0 0 15 15") == some "parameter-stages-shape: omega"
-- groups and stages
#guard why (withLine 14 "group link 3 18 17 17 13") == some "parameter-group-shape: link"
-- every group has the rule 1: a request's, a batch's and a committer's, each with 0 and with 2
#guard why (withLine 14 "group link 0 18 17 17 13") == some "parameter-group-shape: link"
#guard why (withLine 14 "group link 2 18 17 17 13") == some "parameter-group-shape: link"
#guard why (withLine 20 "group own 0 18 14 13 8") == some "parameter-group-shape: own"
#guard why (withLine 20 "group own 2 18 14 13 8") == some "parameter-group-shape: own"
#guard why (withLine 22 "group once-folded 0 17 15 13 6") == some "parameter-group-shape: once-folded"
#guard why (withLine 22 "group once-folded 2 17 15 13 6") == some "parameter-group-shape: once-folded"
#guard why (withLine 14 "group link 1 18 18 17 13") == some "parameter-group-shape: link"
#guard why (withLine 15 "stages link 4 3 17") == some "parameter-stages-count: link"
#guard why (withLine 15 "stages link 4 3 17 17") == some "parameter-stages-shape: link"
#guard why (withLine 15 "stages link 0 0 17 17 0 0 15 15") == some "parameter-stages-shape: link"
#guard why (withLine 15 "stages link 4 5 17 17 0 0 15 15") == some "parameter-stages-shape: link"
-- what several lines show together
#guard why (withLine 20 "group own 1 18 13 13 8") == some "parameter-own-code"
#guard why (withLine 16 "group folded 1 17 15 12 6") == some "parameter-one-mask-code"
-- the table: any radius; more entries than the code is long
#guard why (withLine 31 "table 8 23 524288 65535 2048 11") == some "parameter-table-shape"
#guard why (withLine 31 "table 8 23 524288 65535 524288 11") == some "parameter-table-shape"
#guard why (withLine 31 "table 8 19 524288 65535 0 11") == some "parameter-table-shape"
#guard why (withLine 31 "table 8 23 524288 65535 0 7") == some "parameter-table-shape"
#guard why (withLine 31 "table 8 999999999999999 1 1 0 11") == some "parameter-table-shape"
-- no code is longer than 2 ^ 32: the table's, a group's, a later stage's
#guard why (withLine 31 "table 8 32 524288 65535 0 11") == none
#guard ["table 8 33 524288 65535 0 11", "table 8 40 524288 65535 0 11",
  "table 8 41 524288 65535 0 11"].all fun l =>
  why (withLine 31 l) == some "parameter-table-shape"
#guard why (withLine 14 "group link 1 32 17 17 13") == none
#guard why (withLine 14 "group link 1 33 17 17 13") == some "parameter-group-shape: link"
#guard why (withLine 15 "stages link 3 3 32 16 3 3 15 15 3 3 14 14 3 3 14 13 0 0 16 16") == none
#guard why (withLine 15 "stages link 3 3 33 16 3 3 15 15 3 3 14 14 3 3 14 13 0 0 16 16") ==
  some "parameter-stages-shape: link"
-- the sum of a row's coordinates, from both sides of 2 ^ 32
#guard why (withLine 31 "table 8 32 4294967295 0 0 11") == none
#guard ["table 8 32 4294967295 1 0 11", "table 8 32 1 4294967295 0 11"].all fun l =>
  why (withLine 31 l) == some "parameter-table-shape"

-- a line of a million bytes, and a line of a million values: refused, and the stack holds
#guard why (withLine 1 (String.ofList (List.replicate 1000000 'x'))) ==
  some "parameter-line-order: sec"
#guard why (withLine 15 ("stages link" ++ String.join (List.replicate 1000000 " 1"))) ==
  some "parameter-stages-count: link"

-- the list of the refusals' names: 32 lines; it holds the names that the tests above met
#guard lineHeads.length == 32 && names.length == 4 * 32 + 14 + 3 * 8 + 11
#guard ["parameter-line-missing: table", "parameter-line-order: version",
  "parameter-line-blanks: sec", "parameter-line-values: work field", "parameter-number-spelling",
  "parameter-range: work positions", "parameter-group-shape: link",
  "parameter-stages-count: link", "parameter-stages-shape: link", "parameter-own-code",
  "parameter-one-mask-code", "parameter-table-shape", "version-unknown"].all names.contains

-- the names of the rounds: thirty with the entry that is no round; some kinds
#guard (namesElems ++ namesJoin ++ namesSeeds ++ namesPositions ++ namesEntries ++ namesSealed ++
  namesNothing).length == 29
#guard kindOf "LKP shift" == some .elems && kindOf "SEND answer" == some .nothing &&
  kindOf "RNG" == some .entries && kindOf "LINK" == some .positions && kindOf "RECORD" == none &&
  kindOf "send seed" == none

end OnBytes.Params.TestFile
