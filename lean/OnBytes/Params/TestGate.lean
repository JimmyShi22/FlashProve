-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestGate.lean: tests of the gate on the public files (OnBytes/Params/Gate.lean).

The numbers are those of a small configuration, spelled out here: the 32 lines at the head of a
parameter file, and the codes, shapes and draws of positions that stand in the parameter bytes of
the seven chains which the C++ verifier hashes for a small model under these lines. The model's own
lines are not spelled out; what the tests need of them stands among these numbers. All are written
out and not derived, so the tests are quick and do not rest on the derivation. Every row but the
stored table's has exactly as many random entries as there are draws on it, so one entry less or one
draw more is seen; the table has eight to spare. For the other conditions the cases change a number
to the edge. Below, "the example" means this
configuration. It is an admissible file of the present form, not the default's small plan: its
groups' sizes and stages are their own.

The cases follow blocks/frame/tests/hiding_conditions_test.cpp. The example misses no condition.
For each condition there are numbers that miss it. The word in front of a case is the name under
which the C++ routine reports the condition. A result is a pair: what the part on the links says,
and what the part on the table says.

Where the cases differ from the C++ test. The C++ test lays the plans anew after each change; here
the draws of positions stay as they are. The C++ part on the links asks the leaves of the tests on
the table too; here only the part on the table asks them. The C++ test runs six example files; here
there is one, which is none of the six. Its cases on how often a table's one-time parts were begun,
and on the routine that looks at the parameter file alone, have no counterpart: the verifier asks
neither. The part on the proof of the ranges is tested in OnBytes/Plan/TestRangesGate.lean. Each
test is checked when the file compiles. The file is no part of the program.
-/
import OnBytes.Params.Gate
import OnBytes.Params.TestFile

namespace OnBytes.Params.TestGate

/-! ## The example's numbers -/

/-- The 32 lines at the head of the example's parameter file, written out like the other numbers. -/
def written : List String :=
  ["version H821", "sec 128", "reading 1", "rowcost 1", "slots 64", "answers 1", "record 1",
   "work field 0 0 0", "work sample 0 0 0", "work closeness 0 0 0", "work positions 0 0 0",
   "work smallness 0 0 0", "salt 40", "listed 0",
   "group link 1 18 17 17 13", "stages link 4 3 17 17 3 3 16 16 3 3 15 15 0 0 15 15",
   "group folded 1 17 15 13 6", "stages folded 4 2 14 12 0 0 14 14",
   "group omega 1 18 14 13 6", "stages omega 4 3 14 13 0 0 15 15",
   "group own 1 18 14 13 8", "stages own 4 3 14 13 0 0 15 15",
   "group once-folded 1 17 15 14 6", "stages once-folded 4 2 15 13 0 0 15 15",
   "group once-omega 1 18 14 14 6", "stages once-omega 4 3 15 15 0 0 17 17",
   "group once-own 1 18 14 13 8", "stages once-own 4 3 15 15 0 0 17 17",
   "group once-ranges 1 22 18 16 10", "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20",
   "ranges-part 14", "table 8 23 524288 65535 0 11"]

/-- What these lines say. -/
def lines : Lines := ((readLines (TestFile.fileOf written)).toOption.map (·.1)).getD default

-- the lines are read: without this test a misspelled line would leave the default in their place
#guard (readLines (TestFile.fileOf written)).toOption.isSome

#guard lines.sec == 128 && lines.slots == 64 && lines.answers == 1 &&
  lines.salt == 40 && lines.tableData == 524288 && lines.tableRandom == 65535

/-- The codes of a proof's chains. -/
def codesOfProof : Codes :=
  ⟨#[⟨18, 131072, 259⟩, ⟨17, 8192, 65⟩, ⟨16, 1024, 52⟩, ⟨15, 128, 53⟩, ⟨15, 128, 87⟩,
     ⟨17, 32768, 129⟩, ⟨14, 2048, 88⟩, ⟨18, 16384, 4615⟩, ⟨14, 1024, 90⟩, ⟨15, 1024, 87⟩],
   #[⟨17, 8192, 259⟩, ⟨17, 4096, 65⟩, ⟨16, 2048, 52⟩, ⟨15, 1024, 53⟩, ⟨15, 4096, 87⟩,
     ⟨13, 64, 200⟩, ⟨12, 256, 88⟩, ⟨14, 1024, 88⟩, ⟨13, 1024, 90⟩, ⟨13, 256, 71⟩]⟩

/-- The codes of a key's chains. The last four of each kind are those of the proof of the
ranges. -/
def codesOfKey : Codes :=
  ⟨#[⟨17, 32768, 310⟩, ⟨15, 2048, 247⟩, ⟨15, 2048, 240⟩, ⟨18, 16384, 476⟩, ⟨15, 1024, 230⟩,
     ⟨17, 1024, 224⟩, ⟨22, 262144, 237⟩, ⟨19, 16384, 228⟩, ⟨17, 2048, 224⟩, ⟨20, 2048, 220⟩],
   #[⟨14, 64, 548⟩, ⟨13, 512, 247⟩, ⟨15, 2048, 240⟩, ⟨15, 256, 230⟩, ⟨17, 2048, 224⟩,
     ⟨13, 256, 238⟩, ⟨16, 1024, 237⟩, ⟨17, 512, 228⟩, ⟨17, 256, 224⟩, ⟨20, 2048, 220⟩]⟩

/-- The codes of an entry's chain. -/
def codesOfEntry : Codes :=
  ⟨#[⟨17, 32768, 310⟩, ⟨15, 2048, 247⟩, ⟨15, 2048, 240⟩],
   #[⟨14, 64, 310⟩, ⟨13, 512, 247⟩, ⟨15, 2048, 240⟩]⟩

/-- An oracle message of main rows over the extension field. -/
def rowsE (code rows : Nat) : OracleShape :=
  { code := code, mainRows := rows, mainDeg := 3, maskRows := 0, maskCode := noId, answers := 1 }

/-- An oracle message of mask rows alone. -/
def masksAlone (maskCode rows : Nat) : OracleShape :=
  { code := noId, mainRows := 0, mainDeg := 1, maskRows := rows, maskCode := maskCode,
    answers := 1 }

/-- The stored table. -/
def tableShape : IndexShape := ⟨⟨23, 524288, 65535⟩, 8, 1, 40⟩

/-- The test on the table in a batch. -/
def batchShape : LinShape where
  fold := ⟨tableShape, rowsE 5 18, true, 0, 44⟩
  kLo := 3
  matrixRows := 59392
  omega := rowsE 7 4
  w := rowsE 7 1
  omegaRowsHigh := true
  wRowsHigh := true
  sharedSplit := masksAlone 5 1
  ownSplit := masksAlone noId 0
  omegaLeafClass := 1
  sharedSplitLeafClass := 2
  wLeafClass := 0
  ownSplitLeafClass := 3
  sharedMaskCode := 5
  ownMaskCode := 9
  masksAhead := true
  testU := [⟨5, 5, 5, 0⟩, ⟨6, 6, 4, 2⟩, ⟨6, 7, 0, 0⟩]
  testOmega := [⟨7, 5, 2, 0⟩, ⟨8, 8, 4, 3⟩, ⟨9, 4, 0, 0⟩]
  testOwn := [⟨7, 9, 3, 0⟩, ⟨8, 8, 4, 3⟩, ⟨9, 4, 0, 0⟩]
  testOwnOmega := []
  choice := ⟨true⟩

/-- The committer's own test on the table. -/
def onceShape : LinShape :=
  { batchShape with
    fold := ⟨tableShape, rowsE 0 18, true, 0, 1375⟩
    omega := rowsE 3 4
    w := rowsE 3 1
    sharedSplit := masksAlone 0 1
    sharedMaskCode := 0
    ownMaskCode := 5
    testU := [⟨0, 0, 5, 0⟩, ⟨1, 1, 4, 2⟩, ⟨2, 2, 0, 0⟩]
    testOmega := [⟨3, 0, 2, 0⟩, ⟨4, 3, 4, 3⟩, ⟨5, 4, 0, 0⟩]
    testOwn := [⟨3, 5, 3, 0⟩, ⟨4, 3, 4, 3⟩, ⟨5, 4, 0, 0⟩] }

/-- The link between two tables. -/
def shapeOfLink : LinkShape where
  table := tableShape
  columnsFirst := 44
  columnsFurther := 1375
  code := 0
  maskCode := 0
  rows := 18
  rowsHigh := true
  leafClass := 0
  masksAhead := true
  later := [⟨1, 1, 4, 2⟩, ⟨2, 2, 0, 0⟩]
  choice := ⟨true⟩

/-- An oracle message of a link, from its main rows, their degree, its mask rows, its moment and
its life. -/
def message (rows deg masks moment life : Nat) : ReqMessage :=
  ⟨{ code := 0, mainRows := rows, mainDeg := deg, maskRows := masks,
     maskCode := if masks == 0 then noId else 0, answers := 1 }, 0, moment, life⟩

/-- The five links: two groups of layers, each followed by its attention, and the head. Each has
three moments. -/
def fiveLinks : List ReqLink :=
  [⟨0, [message 61 1 1 0 0, message 3 1 0 0 1, message 1 1 0 0 2, message 2 3 0 1 0,
        message 129 1 0 2 0]⟩,
   ⟨0, [message 23 1 1 0 0, message 1 3 0 1 0, message 61 1 0 2 0]⟩,
   ⟨0, [message 60 1 1 0 0, message 3 1 0 0 1, message 1 1 0 0 2, message 2 3 0 1 0,
        message 129 1 0 2 0]⟩,
   ⟨0, [message 23 1 1 0 0, message 1 3 0 1 0, message 61 1 0 2 0]⟩,
   ⟨1, [message 34 1 1 0 0, message 1 3 0 1 0, message 81 1 0 2 0]⟩]

/-- The rounds that draw positions, by name and number of positions. -/
abbrev Lists : Type := List (String × Nat)

/-- A plan with the given draws of positions. In front of each stands a round that draws no
position. -/
def planOf (draws : Lists) : Planned :=
  ⟨settingOf lines, draws.flatMap fun d =>
    [{ entry := { name := "FOLD round", drawE := 1 } }, { entry := { name := d.1, poss := d.2 } }]⟩

/-! ## A case -/

/-- The numbers that the gate reads. The default values are the example's. -/
structure Case where
  l : Lines := lines
  proof : Codes := codesOfProof
  key : Codes := codesOfKey
  entry : Codes := codesOfEntry
  batch : LinShape := batchShape
  once : LinShape := onceShape
  link : LinkShape := shapeOfLink
  /-- the requests for which the batch's test is sized -/
  requests : Nat := 64
  /-- the batches that a stored copy of the table covers: (65535 - 1375) / 44 -/
  batches : Nat := 1458
  /-- the message whose entries mask a request's rows on the table -/
  batchInput : OracleShape := masksAlone 9 1
  /-- the same for the committer's rows -/
  onceInput : OracleShape := masksAlone 5 1
  /-- the class of leaves of what rides in a request's first message -/
  riderClass : Nat := 1
  /-- the rows on the table that a request's sub-proofs leave -/
  pending : Nat := 3
  /-- the parts of the lookups of the proof of the ranges -/
  parts : Nat := 8
  /-- the scalars that each link's sub-proof sends. This number is made up: with the pad it fills
  the link's mask row of 8192 entries -/
  scalars : Nat := 8191
  first : Lists := [("LOC", 259), ("LOC", 259), ("LOC", 259), ("LOC", 259), ("LOC", 259),
    ("CS", 259), ("CS", 65), ("CS", 52), ("CS", 53), ("BASE", 87)]
  shared : Lists := [("LOC", 44), ("CS", 129), ("CS", 88), ("BASE", 88), ("CS", 71), ("CS", 90),
    ("BASE", 87)]
  second : Lists := [("CS", 71), ("CS", 90), ("BASE", 87)]
  keyShared : Lists := [("LOC", 1375), ("CS", 310), ("CS", 247), ("BASE", 240), ("CS", 238),
    ("CS", 230), ("BASE", 224)]
  keySecond : Lists := [("CS", 238), ("CS", 230), ("BASE", 224)]
  entryLink : Lists := [("LINK", 1419), ("CS", 310), ("CS", 247), ("BASE", 240)]

namespace Case

/-- Sizes of a proximity test that the gate does not read. -/
def noSizes : TestSizes := ⟨{}, 0, []⟩

/-- The sizes of the batch's test. -/
def batchSized (c : Case) : LinSized :=
  { lines := { linLines c.l 59392 1 false with requests := c.requests }, shape := c.batch,
    input := ⟨c.batchInput, 0⟩, table := {}, folded := noSizes, omega := noSizes, own := noSizes,
    batches := c.batches }

/-- The sizes of the committer's test. -/
def onceSized (c : Case) : LinSized :=
  { lines := linLines c.l 59392 1 true, shape := c.once, input := ⟨c.onceInput, 0⟩, table := {},
    folded := noSizes, omega := noSizes, own := noSizes, batches := 0 }

/-- The sizes of a proof's chains. -/
def proofSized (c : Case) : ProofSized :=
  { set := settingOf c.l, codes := c.proof, link := default, last := noSizes,
    request :=
      { code := 0, maskCode := 0, link := fiveLinks, atStart := [⟨c.batchInput, c.riderClass⟩],
        answers := 1, choice := ⟨true⟩,
        last := [⟨0, 0, 1, 0⟩, ⟨1, 1, 4, 3⟩, ⟨2, 2, 3, 3⟩, ⟨3, 3, 3, 3⟩, ⟨4, 4, 0, 0⟩] },
    batch := c.batchSized }

/-- Stand-ins for the sub-proofs. Each sends its scalars over its three moments, with answers and a
root between them, which do not count. -/
def sub (c : Case) : Subproofs :=
  { links := fiveLinks, openRows := [1, 1, 1, 1, 1], pendingRows := c.pending, matrixRows := 59392,
    plan := fun _ moment =>
      if moment == 0 then planScalars (c.scalars - 2)
      else if moment == 1 then do
        planScalars 1
        planAnswers 3
        closeNone "SEND answer"
      else do
        planRoots 1
        planScalars 1 }

/-- What the part on the links says. A refusal counts as a missed condition. -/
def inTheLinks (c : Case) : Bool :=
  (missedInTheLinks c.l c.proofSized c.sub (planOf c.first)).toOption != some false

/-- What the part on the table says. -/
def onTheTable (c : Case) : Bool :=
  missedOnTheTable c.l
    ⟨c.batchSized, c.proof, planOf c.shared, planOf c.second, c.pending, 0⟩
    ⟨c.onceSized, c.key, planOf c.keyShared, planOf c.keySecond, c.parts, c.parts⟩
    ⟨c.link, {}, noSizes⟩ c.entry (planOf c.entryLink)

/-- What the two parts say. -/
def missed (c : Case) : Bool × Bool := (c.inTheLinks, c.onTheTable)

end Case

/-- One random entry less in code number i. -/
def less (l : Array Code) (i : Nat) : Array Code := l.modify i fun c => { c with r := c.r - 1 }

/-- Another length of the messages of code number i. -/
def withEll (l : Array Code) (i ell : Nat) : Array Code := l.modify i fun c => { c with ell := ell }

/-- One position more in draw number i. -/
def more (l : Lists) (i : Nat) : Lists :=
  l.zipIdx.map fun x => if x.2 == i then (x.1.1, x.1.2 + 1) else x.1

/-- Draw number i with n positions. -/
def withDraw (l : Lists) (i n : Nat) : Lists :=
  l.zipIdx.map fun x => if x.2 == i then (x.1.1, n) else x.1

/-- The results of a case for each i below n. -/
def each (n : Nat) (f : Nat → Case) : List (Bool × Bool) := (List.range n).map fun i => (f i).missed

/-! ## Draws and scalars of a plan -/

#guard listsOf (planOf [("LOC", 44), ("CS", 129), ("BASE", 88), ("LINK", 7)]) == [44, 129, 88, 7]
-- a round of another kind is no draw of positions, whatever its entry says
#guard listsOf ⟨settingOf lines, [{ entry := { name := "SEAL", poss := 5 } }]⟩ == []
-- answers and roots are no scalars; a message that no round has taken in counts
#guard (scalarsOf (settingOf lines) (do
    planScalars 5
    planAnswers 2
    closeNone "SEND answer"
    planRoots 2
    planScalars 3)).toOption == some 8
#guard (scalarsOf (settingOf lines) (pure ())).toOption == some 0

/-! ## The example misses nothing; one entry less or one position more is seen -/

#guard ({} : Case).missed == (false, false)

-- main-rows: one random entry less, code by code. The first five codes of a proof are those of its
-- first chain: code 0 is the links' and their last test's first stage's, the rest the later stages'
#guard each 10 (fun i => { proof := { codesOfProof with base := less codesOfProof.base i } }) ==
  List.replicate 5 (true, false) ++ List.replicate 5 (false, true)
-- mask-rows. The last test of the links and the tests on the table share mask code 4
#guard each 10 (fun i => { proof := { codesOfProof with mask := less codesOfProof.mask i } }) ==
  List.replicate 4 (true, false) ++ [(true, true)] ++ List.replicate 5 (false, true)
-- main-rows and mask-rows in a key. The last four codes are read by the part on the ranges alone
#guard each 10 (fun i => { key := { codesOfKey with base := less codesOfKey.base i } }) ==
  List.replicate 6 (false, true) ++ List.replicate 4 (false, false)
#guard each 10 (fun i => { key := { codesOfKey with mask := less codesOfKey.mask i } }) ==
  List.replicate 6 (false, true) ++ List.replicate 4 (false, false)
-- main-rows and mask-rows in an entry
#guard each 3 (fun i => { entry := { codesOfEntry with base := less codesOfEntry.base i } }) ==
  List.replicate 3 (false, true)
#guard each 3 (fun i => { entry := { codesOfEntry with mask := less codesOfEntry.mask i } }) ==
  List.replicate 3 (false, true)

-- one position more, draw by draw, in each of the six chains that the two parts read
#guard each 10 (fun i => { first := more ({} : Case).first i }) == List.replicate 10 (true, false)
#guard each 7 (fun i => { shared := more ({} : Case).shared i }) == List.replicate 7 (false, true)
#guard each 3 (fun i => { second := more ({} : Case).second i }) == List.replicate 3 (false, true)
-- (the table has eight random entries to spare, so one more column in the one-time test is borne)
#guard each 7 (fun i => { keyShared := more ({} : Case).keyShared i }) ==
  (false, false) :: List.replicate 6 (false, true)
#guard each 3 (fun i => { keySecond := more ({} : Case).keySecond i }) ==
  List.replicate 3 (false, true)
#guard each 4 (fun i => { entryLink := more ({} : Case).entryLink i }) ==
  List.replicate 4 (false, true)

-- the links' own rows alone: the last test's first stage draws one position less, so it is content
#guard ({ proof := { codesOfProof with base := less codesOfProof.base 0 },
          first := withDraw ({} : Case).first 5 258 } : Case).missed == (true, false)
#guard ({ proof := { codesOfProof with mask := less codesOfProof.mask 0 },
          first := withDraw ({} : Case).first 5 258 } : Case).missed == (true, false)
#guard ({ first := withDraw ({} : Case).first 5 258 } : Case).missed == (false, false)

-- main-rows: a chain with other lists than one for each link or stage
#guard ({ first := ({} : Case).first.dropLast } : Case).missed == (true, false)
#guard ({ shared := ({} : Case).shared.dropLast } : Case).missed == (false, true)
#guard ({ second := [] } : Case).missed == (false, true)
#guard ({ keySecond := ({} : Case).keySecond ++ [("BASE", 1)] } : Case).missed == (false, true)
#guard ({ entryLink := ({} : Case).entryLink.dropLast } : Case).missed == (false, true)
-- a list too many: every stage finds its list, and the count alone is wrong
#guard ({ first := ({} : Case).first ++ [("BASE", 1)] } : Case).missed == (true, false)
#guard ({ shared := ({} : Case).shared ++ [("BASE", 1)] } : Case).missed == (false, true)
#guard ({ second := ({} : Case).second ++ [("BASE", 1)] } : Case).missed == (false, true)
#guard ({ keyShared := ({} : Case).keyShared ++ [("BASE", 1)] } : Case).missed == (false, true)
#guard ({ entryLink := ({} : Case).entryLink ++ [("BASE", 1)] } : Case).missed == (false, true)

/-! ## Leaves -/

-- the fresh mask of the batch's test on the second oracle message, in that message's leaves
#guard missedInLeaves [(⟨batchShape.omega, 1⟩, 6),
  ((linMaskNotice batchShape.testOmega 1).getD default, 2)]
#guard !missedInLeaves [(⟨batchShape.omega, 1⟩, 6),
  ((linMaskNotice batchShape.testOmega 101).getD default, 2)]
-- one class and the same lists
#guard !missedInLeaves [(⟨batchShape.omega, 1⟩, 6),
  ((linMaskNotice batchShape.testOmega 1).getD default, 6)]
#guard !missedInTheTablesLeaves batchShape && !missedInTheTablesLeaves onceShape
-- the masks that part a row between two groups, in the second oracle message's leaves
#guard ({ batch := { batchShape with sharedSplitLeafClass := 1 } } : Case).missed == (false, true)
#guard ({ once := { onceShape with sharedSplitLeafClass := 1 } } : Case).missed == (false, true)
-- a request's own vector under another code than the second oracle message's
#guard missedInTheTablesLeaves { batchShape with w := rowsE 8 1 }
-- what rides in a request's first message, in the class of the links' messages
#guard ({ riderClass := 0 } : Case).missed == (true, false)

/-! ## Pads, mask room, fold room -/

-- padding-entries: 18 rows of 32768 entries hold a row of the table, 524288 + 65535 entries, and
-- one pad
#guard ({ batch := { batchShape with fold := { batchShape.fold with u := rowsE 5 17 } } } :
  Case).missed == (false, true)
#guard ({ batch := { batchShape with omega := rowsE 7 3 } } : Case).missed == (false, true)
#guard ({ once := { onceShape with w := rowsE 3 0 } } : Case).missed == (false, true)
-- padding-entries: room for the data and none for the pad. 18 * 32768 = 524288 + 65536;
-- 4 * 16384 = 65536; 16384 = 2^(8 + 6)
#guard ({ l := { lines with tableRandom := 65536 } } : Case).missed == (false, true)
#guard ({ batch := { batchShape with matrixRows := 65535 } } : Case).missed == (false, false)
#guard ({ batch := { batchShape with matrixRows := 65536 } } : Case).missed == (false, true)
#guard ({ batch := { batchShape with kLo := 6 } } : Case).missed == (false, true)
-- padding-entries: three places off the matrix's 59392 * 8 for each answer
#guard ({ l := lines } : Case).missed == (false, false)
#guard ({ l := { lines with tableData := 475139 } } : Case).missed == (false, false)
#guard ({ l := { lines with tableData := 475138 } } : Case).missed == (false, true)

-- mask-room: no entry for the masks that part a row; none for the rows on the table
#guard ({ batch := { batchShape with sharedSplit := masksAlone 5 0 } } : Case).missed ==
  (false, true)
#guard ({ onceInput := masksAlone 5 0 } : Case).missed == (false, true)
#guard ({ batchInput := masksAlone 9 0 } : Case).missed == (false, true)
-- mask-room in a key: two entries for each of 8 parts, 1 + 2 * 11 for the joining, one pad: 40
#guard ({ key := { codesOfKey with mask := withEll codesOfKey.mask 5 40 } } : Case).missed ==
  (false, false)
#guard ({ key := { codesOfKey with mask := withEll codesOfKey.mask 5 39 } } : Case).missed ==
  (false, true)
-- mask-room in a batch: the pending rows, 23 for the joining and one pad in 256 entries
#guard ({ pending := 232 } : Case).missed == (false, false)
#guard ({ pending := 233 } : Case).missed == (false, true)
-- one pending row needs no joining. 7 entries: the least that the own test's first fold bears
#guard ({ pending := 1, proof := { codesOfProof with mask := withEll codesOfProof.mask 9 7 } } :
  Case).missed == (false, false)
-- mask-room in a link: the sub-proof's scalars and one pad in 8192 entries
#guard ({ scalars := 8192 } : Case).missed == (true, false)

-- fold-room: the first link's group has 9 row variables and none for mask rows: 19 entries
#guard ({ scalars := 3, proof := { codesOfProof with mask := withEll codesOfProof.mask 0 19 } } :
  Case).missed == (false, false)
#guard ({ scalars := 3, proof := { codesOfProof with mask := withEll codesOfProof.mask 0 18 } } :
  Case).missed == (true, false)
-- fold-room in a test on the table: 2 * 5 + 1 entries
#guard ({ proof := { codesOfProof with mask := withEll codesOfProof.mask 5 11 } } : Case).missed ==
  (false, false)
#guard ({ proof := { codesOfProof with mask := withEll codesOfProof.mask 5 10 } } : Case).missed ==
  (false, true)
-- a stage with mask rows: 2 * 4 + 1 - 2 entries
#guard ({ proof := { codesOfProof with mask := withEll codesOfProof.mask 6 7 } } : Case).missed ==
  (false, false)
#guard ({ proof := { codesOfProof with mask := withEll codesOfProof.mask 6 6 } } : Case).missed ==
  (false, true)

/-! ## Table, salt, batch -/

-- table: 1375 + 1458 * 44 = 65527 of 65535 columns
#guard ({ batches := 1459 } : Case).missed == (false, true)
#guard ({ l := { lines with tableRandom := 65527 } } : Case).missed == (false, false)
#guard ({ l := { lines with tableRandom := 65526 } } : Case).missed == (false, true)
-- table: the larger of what the one-time test and a further copy's link open. Eight are to spare
#guard ({ keyShared := withDraw ({} : Case).keyShared 0 1383 } : Case).missed == (false, false)
#guard ({ keyShared := withDraw ({} : Case).keyShared 0 1384 } : Case).missed == (false, true)
#guard ({ link := { shapeOfLink with columnsFurther := 1383 },
          entryLink := withDraw ({} : Case).entryLink 0 1427 } : Case).missed == (false, false)
#guard ({ link := { shapeOfLink with columnsFurther := 1384 },
          entryLink := withDraw ({} : Case).entryLink 0 1428 } : Case).missed == (false, true)
-- table: a link draws other numbers of columns than its shape says
#guard ({ link := { shapeOfLink with columnsFirst := 43 } } : Case).missed == (false, true)
-- salt
#guard ({ l := { lines with salt := 39 } } : Case).missed == (true, true)
-- batch
#guard ({ requests := 63 } : Case).missed == (false, true)

/-! ## Range checks -/

/-- The C++ test's stand-in: 2^14 rows of 2^16 cells below 41; digits for -2^17 to 2^17 - 1. -/
def standIn : RangeCheck := ⟨2 ^ 14, 2 ^ 16, 128, 41, 2 ^ 17, (10, 8)⟩

/-- 25 checks, of which number 7 is changed. -/
def checks (f : RangeCheck → RangeCheck) : List RangeCheck :=
  (List.replicate 25 standIn).set 7 (f standIn)

/-- The part on the range checks at these numbers:
128 bits, 64 requests in a batch, 44040191
random entries in a row of the table, 232 columns in the one-time test. The C++ test says of two
further numbers only that their logarithms round up to 20: the batches of a stored copy and the
copies. 2^20 batches and 42 columns of a link give these. -/
def inTheChecks (c : List RangeCheck) : Bool :=
  missedInTheChecks { lines with tableRandom := 44040191 } c 232 42 (2 ^ 20)

-- 2^34 / (2^16 * 1600) = 163.84; times 1.4426: 236; less 1 + 14 + 7
#guard rangeCheckBits standIn == some 214
#guard !inTheChecks (checks id)
#guard inTheChecks []
-- 72.8 * 1.4426 = 105 bits, less 22
#guard rangeCheckBits { standIn with bound := 61 } == some 83
#guard inTheChecks (checks ({ · with bound := 61 }))
#guard rangeCheckBits { standIn with bound := 1 } == none
#guard inTheChecks (checks ({ · with bound := 1 }))
-- the edge: 179 and 178 bits, less 5 for 25 checks, 6 for 64 requests, 20 and 20: 128 and 127
#guard rangeCheckBits { standIn with columns := 77063 } == some 179
#guard !inTheChecks (checks ({ · with columns := 77063 }))
#guard rangeCheckBits { standIn with columns := 77064 } == some 178
#guard inTheChecks (checks ({ · with columns := 77064 }))
-- digits for -2^17 to 3 * 2^17 - 1
#guard rangeCheckBits { standIn with digitBits := (10, 9) } == none
#guard inTheChecks (checks ({ · with digitBits := (10, 9) }))
-- each factor is rounded up by itself: one check more than a power of two costs a bit
#guard !missedInTheChecks { lines with tableRandom := 44040191 }
  (List.replicate 32 { standIn with columns := 77063 }) 232 42 (2 ^ 20)
#guard missedInTheChecks { lines with tableRandom := 44040191 }
  (List.replicate 33 { standIn with columns := 77063 }) 232 42 (2 ^ 20)
#guard missedInTheChecks { lines with tableRandom := 44040191 }
  (checks ({ · with columns := 77063 })) 232 42 (2 ^ 20 + 1)
#guard missedInTheChecks { lines with tableRandom := 44040191 }
  (checks ({ · with columns := 77063 })) 232 41 (2 ^ 20)
-- fewer random entries than the one-time test opens: one copy. No batch costs no bit
#guard !missedInTheChecks { lines with tableRandom := 100 } (checks id) 232 0 0
-- a link without columns counts as one with one column: 44039960 copies, 26 bits. 150 bits, less
-- 5 + 6 + 0 + 26, are 113
#guard rangeCheckBits { standIn with columns := 90000 } == some 150
#guard missedInTheChecks { lines with tableRandom := 44040191 }
  (checks ({ · with columns := 90000 })) 232 0 1

-- numbers out of range
#guard [{ standIn with rows := 0 }, { standIn with columns := 0 },
  { standIn with combinations := 0 }, { standIn with range := 0 },
  { standIn with rows := 2 ^ 40 }, { standIn with columns := 2 ^ 32 },
  { standIn with combinations := 2 ^ 16 }, { standIn with bound := 2 ^ 32 },
  { standIn with range := 2 ^ 40, digitBits := (20, 21) },
  { standIn with range := 2 ^ 41, digitBits := (21, 21) }].all fun c => rangeCheckBits c == none
-- the largest numbers that are served
#guard rangeCheckBits { standIn with range := 2 ^ 39, digitBits := (20, 20) } == some (2 ^ 30)
#guard rangeCheckBits ⟨2 ^ 40 - 1, 2 ^ 32 - 1, 2 ^ 16 - 1, 2 ^ 32 - 1, 2 ^ 39, (0, 40)⟩ ==
  some (-57)
-- a check that fails too often has a negative number of bits, and the condition is missed
#guard rangeCheckBits { standIn with columns := 2 ^ 32 - 1 } == some (-22)
#guard inTheChecks (checks ({ · with columns := 2 ^ 32 - 1 }))

end OnBytes.Params.TestGate
