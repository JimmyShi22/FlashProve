-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestItems.lean: tests of the readers and spellers of the parameter items, of the
readers of whole parameter bytes, of the chains' statements (that of a proof's first chain with two
known answers) and of the seven chains' labels.

The records are made up. Each test is checked when the file compiles. The file is no part of the
program.
-/
import OnBytes.Params.Chains
import OnBytes.Params.Spell

namespace OnBytes.Params.TestItems

/-- Made-up codes. -/
def codes : Codes := ⟨#[⟨6, 4, 2⟩, ⟨7, 2, 2⟩], #[⟨6, 16, 2⟩]⟩

/-- A shape with main rows alone. -/
def mainOnly : OracleShape :=
  { code := 1, mainRows := 3, mainDeg := 3, maskRows := 0, maskCode := noId, answers := 1 }
/-- A shape with mask rows alone. -/
def maskOnly : OracleShape :=
  { code := noId, mainRows := 0, mainDeg := 1, maskRows := 2, maskCode := 0, answers := 1 }
/-- The shape of a message that does not exist. -/
def noRows : OracleShape :=
  { code := noId, mainRows := 0, mainDeg := 1, maskRows := 0, maskCode := noId, answers := 1 }

/-- A stored table's shape. -/
def table : IndexShape := ⟨⟨4, 5, 3⟩, 1, 0, 40⟩

/-- An item "the test on the table". -/
def lin : LinShape :=
  { fold := ⟨table, mainOnly, true, 0, 7⟩, kLo := 2, matrixRows := 9, omega := mainOnly,
    w := mainOnly, omegaRowsHigh := true, wRowsHigh := false, sharedSplit := maskOnly,
    ownSplit := noRows, omegaLeafClass := 1, sharedSplitLeafClass := 2, wLeafClass := 0,
    ownSplitLeafClass := 3, sharedMaskCode := 0, ownMaskCode := 0, masksAhead := true,
    testU := [⟨0, 0, 2, 0⟩, ⟨1, 0, 0, 0⟩], testOmega := [], testOwn := [⟨0, 0, 1, 0⟩],
    testOwnOmega := [], choice := ⟨true⟩ }

/-- An item "the link". -/
def link : LinkShape :=
  { table := table, columnsFirst := 2, columnsFurther := 3, code := 0, maskCode := 0, rows := 3,
    rowsHigh := true, leafClass := 0, masksAhead := true, later := [⟨1, 0, 0, 0⟩],
    choice := ⟨false⟩ }

/-- An item "ranges". -/
def ranges : WfPublic :=
  { lookups := [{ d := 8, mu := 5, live := 28, digitWeight := [1, 256], offset := 128,
                  paddingKey := 0, parts := [⟨3, [⟨0, 0, 5, 5⟩, ⟨5, 9, 2, 2⟩]⟩, ⟨3, []⟩],
                  firstBound := [2, 1, 0] }],
    message := ⟨{ mainOnly with maskRows := 7, maskCode := 0 }, 0⟩, messageId := 1,
    stages := [⟨0, 0, 3, 3⟩, ⟨1, 0, 0, 0⟩], choice := ⟨true⟩ }

/-- A chain of two links. -/
def req : ReqShape :=
  { code := 0, maskCode := 0,
    link := [⟨0, [⟨{ code := 0, mainRows := 2, mainDeg := 1, maskRows := 1, maskCode := 0,
                     answers := 1 }, 0, 0, 0⟩,
                  ⟨{ code := 0, mainRows := 1, mainDeg := 1, maskRows := 0, maskCode := noId,
                     answers := 1 }, 0, 0, 1⟩]⟩,
             ⟨1, [⟨{ code := 0, mainRows := 1, mainDeg := 3, maskRows := 0, maskCode := noId,
                     answers := 1 }, 0, 1, 0⟩]⟩],
    atStart := [⟨maskOnly, 1⟩], answers := 1, last := [⟨0, 0, 1, 0⟩, ⟨1, 0, 0, 0⟩],
    choice := ⟨true⟩ }

/-- An item "layout". -/
def layout : ReqLayout :=
  ⟨[[⟨"M0", 0, 3, 4, [⟨0, 0, 0, 0, 2, 2, 1, 3, true⟩]⟩, ⟨"U3", 1, 1, 1, []⟩], []]⟩

-- what is spelled is read back
#guard readCodes (spellCodes codes) == some codes
#guard [mainOnly, maskOnly, noRows].all fun o => readNotice (spellNotice ⟨o, 5⟩) == some ⟨o, 5⟩
#guard readLin (spellLin lin) == some lin
#guard readLink (spellLink link) == some link
#guard readBinding (spellBinding ⟨6, 40⟩) == some ⟨6, 40⟩
#guard readRanges (spellRanges ranges) == some ranges
#guard readReq (spellReq req) == some req
#guard readLayout (spellLayout layout) == some layout
#guard readWords (spellWords [3, 1, 2]) == some [3, 1, 2]
#guard readWord (spellWord 13) == some 13
-- a byte less or more
#guard (readLin ((spellLin lin).extract 0 ((spellLin lin).size - 1))).isNone
#guard (readLin (spellLin lin ++ Fmt.zeroBytes 1)).isNone
#guard (readLayout (spellLayout layout ++ Fmt.zeroBytes 8)).isNone
-- one shape has one spelling: a code's number where there are no rows; a degree 3 without main
-- rows; a degree 2
#guard (readNotice (spellRow [1, noId, 0, 1, 0, 1, 0])).isNone
#guard (readNotice (spellRow [noId, 0, 0, 1, 0, 1, 0])).isNone
#guard (readNotice (spellRow [noId, noId, 0, 3, 0, 1, 0])).isNone
#guard (readNotice (spellRow [1, noId, 3, 2, 0, 1, 0])).isNone
-- a word of yes or no that is 2
#guard (readFlag (spellWord 2)).isNone && readFlag (spellWord 1) == some true
-- an element of the base field that is not below the prime
#guard (readRanges (spellRanges { ranges with
  lookups := ranges.lookups.map (fun l => { l with offset := 0xFFFFFFFF00000001 }) })).isNone
-- a length word beyond the end
#guard (readWords (spellWord 3 ++ spellRow [1, 2])).isNone
-- an oracle message that is kept beyond the last link
#guard (readReq (spellReq { req with link := req.link.take 1 })).isNone

/-- A made-up plan of two rounds. -/
def plan : Fmt.Plan :=
  { field := .two, salt := 40, nonce := 8, posB := 0, samples := 1, saved := 1,
    entries := [{ name := "ZERO", drawE := 2 }, { name := "LAST", msg := 24 }] }

/-- Parameter bytes with this plan and given items. -/
def params (items : List (String × ByteArray)) (p : Fmt.Plan := plan) : ByteArray :=
  Fmt.paramsBytes p Fmt.zero32 items

-- whole parameter bytes: read; the rounds; an item by its name
#guard (Given.read (params [("codes", spellCodes codes)])).any fun g =>
  g.rounds.map (·.name) == ["ZERO", "LAST"] && (g.item "codes").bind readCodes == some codes &&
  g.under Fmt.zero32 && g.lists.isEmpty
-- a round's name that is none of the format's
#guard (Given.read (params [] { plan with entries := [{ name := "zero", drawE := 2 }] })).isNone
-- the chains: their items by name and in their order
#guard (Shared.read (params [("codes", spellCodes codes),
  ("the test on the table", spellLin lin)])).isSome
#guard (Shared.read (params [("the test on the table", spellLin lin),
  ("codes", spellCodes codes)])).isNone
#guard (Shared.read (params [("codes", spellCodes codes)])).isNone
#guard (Second.read (params [])).isSome &&
  (Second.read (params [("codes", spellCodes codes)])).isNone
#guard (Link.read (params [("codes", spellCodes codes), ("the link", spellLink link)])).isSome
#guard (OneTime.read (params [("index-mask message", spellNotice ⟨maskOnly, 0⟩),
  ("ranges", spellRanges ranges), ("binding tree", spellBinding ⟨0, 40⟩),
  ("codes", spellCodes codes), ("the test on the table", spellLin lin)])).isSome

/-- The items of a proof's first chain. -/
def firstItems (r : ReqShape) (ids : List Nat) (pending : Nat) : List (String × ByteArray) :=
  [("codes", spellCodes codes), ("the test on the table", spellLin lin),
   ("request's shape", spellReq r), ("layout", spellLayout layout),
   ("links' identifiers", spellWords ids), ("pending rows", spellWord pending),
   ("binding tree", spellBinding ⟨6, 40⟩)]

#guard (First.read (params (firstItems req [1, 2] 3))).isSome
-- no items of a proof: an identifier too few; no pending row; no rider
#guard (First.read (params (firstItems req [1] 3))).isNone
#guard (First.read (params (firstItems req [1, 2] 0))).isNone
#guard (First.read (params (firstItems { req with atStart := [] } [1, 2] 3))).isNone
-- the statements' bytes: lengths
#guard (OneTime.statement ⟨Fmt.zero32, []⟩).size == 8 + 5 + 8 + 40 + 8
#guard (Second.statement Fmt.zero32 Fmt.zero32).size == 2 * (8 + 28 + 8 + 32)
-- a proof's first chain: four items; the last one byte for byte: the name as a text, the length of
-- the value, the value as a string of bytes (R14.3, R4.1, R1.6)
#guard (First.statement ⟨Fmt.zero32, []⟩ 7 ⟨#[1]⟩ ⟨#[2, 3]⟩).size ==
  (8 + 5 + 8 + 40 + 8) + (8 + 11 + 8 + 8) + (8 + 7 + 8 + (8 + 1)) + (8 + 24 + 8 + (8 + 2))
#guard First.statement ⟨Fmt.zero32, []⟩ 7 ⟨#[1]⟩ ⟨#[2, 3]⟩ ==
  OneTime.statement ⟨Fmt.zero32, []⟩ ++ Fmt.item "stored copy" (Fmt.u64n 7) ++
    Fmt.item "request" (Fmt.u64n 1 ++ ⟨#[1]⟩) ++
    (Fmt.u64n 24 ++ "the request file's words".toUTF8 ++ Fmt.u64n 10 ++ Fmt.u64n 2 ++ ⟨#[2, 3]⟩)
#guard "the request file's words".toUTF8.size == 24
-- a known answer of the format's own script (docs/format/format-vectors.txt, line 184): the
-- statement of its first chain: the table's root pattern(32), no answers; the copy 1; the request
-- 01 02 03 04; the request file's words 05 06 07 08
#guard First.statement ⟨Fmt.pattern 32, []⟩ 1 ⟨#[1, 2, 3, 4]⟩ ⟨#[5, 6, 7, 8]⟩ == Fmt.unhex
  "05000000000000007461626c6530000000000000002000000000000000030a11181f262d343b424950575e65\
    6c737a81888f969da4abb2b9c0c7ced5dc00000000000000000b0000000000000073746f72656420636f7079\
    080000000000000001000000000000000700000000000000726571756573740c000000000000000400000000\
    00000001020304180000000000000074686520726571756573742066696c65277320776f7264730c00000000\
    000000040000000000000005060708"
-- a second known answer of the format's own script (docs/format/format_rules.py, proof_statement;
-- not a line of format-vectors.txt): another root, no answers; the copy 1; the item "request" and
-- the request file's words have one value, 01 02 03 04, so this test does not see the order of the
-- two. The root stands for any 32 bytes: it is the root of a small table over made-up data that a
-- test run of the C++ programs made; it is no stored example's and stands in no file of this tree
#guard First.statement
    ⟨Fmt.unhex "3a2efe4d4c9ceb7aaa6ecbf67dbceeaa60137c8cd57dbe9f26beecd286ea4ea4", []⟩ 1
    ⟨#[1, 2, 3, 4]⟩ ⟨#[1, 2, 3, 4]⟩ == Fmt.unhex
  "05000000000000007461626c65300000000000000020000000000000003a2efe4d4c9ceb7aaa6ecbf67dbcee\
    aa60137c8cd57dbe9f26beecd286ea4ea400000000000000000b0000000000000073746f72656420636f7079\
    080000000000000001000000000000000700000000000000726571756573740c000000000000000400000000\
    00000001020304180000000000000074686520726571756573742066696c65277320776f7264730c00000000\
    000000040000000000000001020304"
-- the two strings of bytes stand in two items: passed in the other order they give other bytes
#guard First.statement ⟨Fmt.zero32, []⟩ 7 ⟨#[1]⟩ ⟨#[2]⟩ !=
  First.statement ⟨Fmt.zero32, []⟩ 7 ⟨#[2]⟩ ⟨#[1]⟩
-- the seven chains' labels: their values (a proof's shared and second chain: R14.9, R14.10), and
-- that no two are the same. The record's label, 2^32 (R4.8; `Fmt.recordLabel`), is no label of a
-- file's chain and is not in the list: each of the seven is below 2^32
#guard [labelFirst, labelOneTime, labelShared, labelSecond, labelSharedProof, labelSecondProof,
    labelLink] ==
  [0x46524d01, 0x46524d02, 0x4c494e01, 0x4c494e02, 0x46524d03, 0x46524d04, 0x4c4e4b01]
#guard [labelFirst, labelOneTime, labelShared, labelSecond, labelSharedProof, labelSecondProof,
    labelLink].eraseDups.length == 7
-- the test of the test: with a key's label in a proof's place the count falls
#guard [labelFirst, labelOneTime, labelShared, labelSecond, labelShared, labelSecondProof,
    labelLink].eraseDups.length == 6

end OnBytes.Params.TestItems
