-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestRecordWork.lean: the planner's numbers at the setting "record with work", and what
the stages' accounting counts for the committer's files.

The setting: all eight groups up to the Johnson radius, proof of work before the draws of positions
(20, 28, 32 bits), and a stored table with a record. The small files are copies of the three public
files of prover/examples/target_small_f2_roomy: policy.txt, 183 lines (sha256 8d9ae1dd...; its first
32 lines are typed here, its later lines are those of the copy in
OnBytes/Params/SmallFiles.lean), and that file's copies of KL.bin and layout.txt, which
are the same files. One run of `planned` on them gives the seven chains, and one test holds what is
seen (`Seen`). Held against what the C++ verifier cp_verify printed for these files in its planning
call (`-plan accounting`, 128 bits): the digest in the line `configuration=`; the sum of the seven
numbers of rounds, 11857; the closeness rounds by source for key, entry and proof, and for all three
files; of all three files the rounds that hold only with their work, 38, the pair 96.23 + 32, and
128.00 with work; the length, rows and positions of all 30 stages of the nine tests; the positions
and the integer m of the links' group; the four numbers of columns and the batches; the digest in the line `h_par=`. From a copy of the
verifier that writes out what it hashes: the length and the digest of the entry's parameter bytes,
against what the command `plan` gives. This program's
own, compared with no print: the seven numbers of rounds one by one; for key, entry and proof by
themselves the last four numbers of `sums`; the three conditions in `form`; the table's two derived
integers; the entry RECORD; the rounds as read back. The second part runs the accounting of plans
(`oneTime`) on the setting itself. The third part holds what follows from the 32 first
lines of prover/examples/target_full_f2/policy.txt alone (sha256 of these lines 98ba1ef1...): what
they say, and the entry's plan, test, columns and table; cp_verify printed the same 23 closeness
rounds, five stages and columns for the full-size files. The other numbers of that test are this
program's own. Each test is checked when the file compiles, by Lean's evaluator. The file is no part
of the program.

What is not tested here: that the copies are any example's files (nothing in OnBytes/ reads a folder
of examples), and cp_verify itself: no test runs it, and its prints are kept in no file of this
tree. No key, entry or proof file is checked. No stage is run: that the stages key and leaf call
`Common.acct` with these plans is not tested. Every file here has `work sample 0 0 0`, where the
bare target and the goal for samples are one number: no test here holds that `sizeRecordedTable`
compares the record's round with the former. At the full size nothing on a key's or a proof's plans,
which need the full-size layout file. `commonFor` fills the two fields that `Common.acct` does not
read with empty values.
-/
import OnBytes.Model.Verify
import OnBytes.Params.SmallFiles
import OnBytes.Hash.H

namespace OnBytes.Model.Verify.TestRecordWork

open OnBytes.Params

/-- The first 32 lines of the small parameter file. -/
def smallHead : List String :=
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

/-- The first 32 lines of the full-size parameter file. -/
def fullHead : List String :=
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

/-- A small parameter file: 32 first lines, then the later lines of the small file of this
setting. -/
def policyOf (head : List String) : ByteArray :=
  ("\n".intercalate (head ++ SmallFiles.policyTail.splitOn "\n")).toUTF8

/-- The lines with some of them replaced: each pair is a line and what stands in its place. -/
def turned (head : List String) (pairs : List (String × String)) : List String :=
  head.map fun l => (pairs.lookup l).getD l

/-- For each stage of a test: the logarithm of the main code's length, that of the number of main
rows, and the positions. -/
def stagesOf (t : TestSizes) : List (Nat × Nat × Nat) :=
  t.stages.map fun x => (x.g.main.logN, x.g.k, x.t)

/-- Of the accounting of some chains' plans: the closeness rounds on the lemma within a third and on
the assumed theorem; the rounds that hold only with their work; the largest
error without work in hundredths of a bit, with its round's bits of work; the largest error with
work. -/
def sums (s : Setting) (plans : List Params.Planned) :
    Nat × Nat × Nat × Nat × Nat × Nat :=
  let a := account (merged s plans)
  (a.closeThird, a.closeJohnson, a.byWork,
    (a.lists.map fun l => centibits l.error).getD 0, (a.lists.map (·.work)).getD 0,
    (a.withWork.map centibits).getD 0)

/-- The entries of a plan under the name RECORD, by their eleven numbers. -/
def records (P : Params.Planned) : List (List Nat) :=
  (P.plan.entries.filter fun e => e.name == Fmt.recordName).map fun e =>
    [e.count, e.work, e.msg, e.roots, e.answers, e.drawE, e.drawNZ, e.poss, e.logN, e.trits, e.rows]

/-- What `planned` returns on a small parameter file with the small scales and layout. -/
def plannedAt (head : List String) : Option Planned :=
  (planned (policyOf head) SmallFiles.scales
    (some SmallFiles.layout)).toOption

/-- What the stages key and leaf have in common, as far as their accounting reads it. The key's
table and the commitment's ID are not read by `Common.acct`. -/
def commonFor (p : Planned) : Common :=
  { X := p.X, chains := p.chains, built := p.built, first := ⟨ByteArray.empty, []⟩, idHex := "" }

/-- Of the key's plans and of the entry's plan, the closeness rounds by source (the lemma within a
third, the assumed theorem). -/
def oneTime (head : List String) : Option ((Nat × Nat) × (Nat × Nat)) :=
  (plannedAt head).map fun p =>
    let m := p.chains.made
    let three := fun (plans : List Params.Planned) =>
      let a := account (merged m.sized.set plans)
      (a.closeThird, a.closeJohnson)
    (three m.key, three [m.entry])

/-- All that is held of the small files, in one run of `planned`. -/
structure Seen where
  configuration : String
  rounds : List Nat
  sums : List (Nat × Nat × Nat × Nat × Nat × Nat)
  form : Bool × Bool × Bool
  stages : List (List (Nat × Nat × Nat))
  numbers : List Nat
  table : List Nat
  records : List (List (List Nat))
  readBack : List Nat
  deriving BEq, Repr

/-- What is seen at the small files. -/
def seen : Option Seen :=
  (plannedAt smallHead).map fun p =>
    let c := p.chains
    let m := c.made
    let z := m.sized
    let all := m.key ++ [m.entry] ++ m.proof
    let T := z.key.once.table
    { configuration := Fmt.hex p.cfg
      rounds := all.map (·.rounds.length)
      sums := [sums z.set m.key, sums z.set [m.entry], sums z.set m.proof, sums z.set all]
      form := (p.X.P.frame.reading == 1, c.twoCodes, p.X.recordOneAnswer)
      stages := [stagesOf z.proof.last, stagesOf z.proof.batch.folded, stagesOf z.proof.batch.omega,
        stagesOf z.proof.batch.own, stagesOf z.key.once.folded, stagesOf z.key.once.omega,
        stagesOf z.key.once.own, stagesOf z.key.ranges.test, stagesOf z.link.linked]
      numbers := [z.proof.link.t, z.proof.link.group.m, z.key.once.shape.fold.columns,
        z.link.shape.columnsFirst, z.link.shape.columnsFurther, z.proof.batch.shape.fold.columns,
        z.proof.batch.batches]
      table := [T.answers, T.distances.radius, T.distances.laterRadius,
        T.distances.mOnce, T.distances.mLater]
      records := all.map records
      readBack := [c.key.oneTime.given.rounds.length, c.key.shared.given.rounds.length,
        c.key.second.given.rounds.length, c.link.given.rounds.length,
        c.proof.first.given.rounds.length, c.proof.shared.given.rounds.length,
        c.proof.second.given.rounds.length] }

#guard (policyOf smallHead).size == 2479
#guard seen == some
  { -- cp_verify's line configuration=
    configuration := "ee76db0af2ce5af0a9b9d27398aac0adfafc2c5a4c2fb5643bb6a9bcb2535a56"
    -- key (three chains), entry, proof (three); cp_verify prints their sum, 11857
    rounds := [3679, 42, 16, 25, 8037, 42, 16]
    -- key, entry, proof, all: every closeness round rests on the assumed theorem
    sums := [(0, 37, 14, 9623, 32, 12800), (0, 12, 4, 9650, 32, 12800),
      (0, 78, 20, 10011, 28, 12800), (0, 127, 38, 9623, 32, 12800)]
    -- reading-as-printed, two-codes, record-one-answer
    form := (true, true, true)
    -- the nine tests in the order of cp_verify's lines group:
    stages := [[(18, 1, 218), (17, 4, 55), (16, 3, 44), (15, 3, 44), (15, 0, 73)],
      [(17, 5, 101), (14, 4, 68), (14, 0, 68)], [(18, 2, 55), (14, 4, 69), (15, 0, 68)],
      [(18, 3, 59), (14, 4, 75), (15, 0, 73)], [(17, 5, 97), (14, 4, 66), (14, 0, 66)],
      [(18, 2, 49), (14, 4, 49), (15, 0, 39)], [(18, 3, 49), (14, 4, 49), (15, 0, 39)],
      [(22, 3, 49), (19, 4, 39), (17, 3, 33), (20, 0, 22)],
      [(17, 6, 97), (14, 4, 66), (14, 0, 66)]]
    -- the links' group: positions, m; columns: one-time, a link's two, a batch; the batches
    numbers := [218, 517, 51, 51, 51, 53, 1235]
    -- a record of one answer; no radius from the line; the two derived integers
    table := [1, 0, 0, 82, 82]
    -- RECORD stands in the key's one-time plan and in the entry's plan, and in no other
    records := [[[1, 0, 0, 0, 0, 20, 1, 0, 0, 0, 0]], [], [], [[1, 0, 0, 0, 0, 20, 1, 0, 0, 0, 0]],
      [], [], []]
    -- a chain's rounds as read back are the entries but for RECORD
    readBack := [3678, 42, 16, 24, 8037, 42, 16] }

/-! ## The committer's files, by the stages' own accounting -/

-- all eight groups at the Johnson radius
#guard oneTime smallHead == some ((0, 37), (0, 12))

/-! ## The full size: what follows from the 32 lines alone -/

/-- What the full-size file's first 32 lines say. -/
def fullLinesRead : Option Lines :=
  (readLines ("\n".intercalate fullHead ++ "\n").toUTF8).toOption.map (·.1)

#guard fullLinesRead.map (fun l => (l.workPositions.request, l.workPositions.shared,
    l.workPositions.once)) ==
  some (20, 28, 32)
-- the entry's plan, its test stage by stage, a link's columns, the table as sized
#guard (fullLinesRead.bind fun l => (entrySized l).toOption).map (fun y =>
    (y.2.2.rounds.length, sums y.2.2.set [y.2.2], records y.2.2, stagesOf y.1.linked,
      y.1.shape.columnsFirst, y.1.shape.columnsFurther,
      [y.1.table.answers, y.1.table.distances.radius, y.1.table.distances.laterRadius,
        y.1.table.distances.mOnce, y.1.table.distances.mLater])) ==
  some (42, (0, 23, 6, 9623, 32, 12800), [[1, 0, 0, 0, 0, 30, 1, 0, 0, 0, 0]],
    [(24, 8, 97), (21, 5, 49), (17, 4, 49), (13, 4, 50), (14, 0, 40)], 62, 62,
    [1, 0, 0, 24, 24])

/-! ## The digest h_par and the command `plan` on the small files -/

/-- What the command `plan` gives for the entry's chain, on these scales. -/
def planEntryAt (scales : ByteArray) : Option ByteArray :=
  (planBytes 128 (some (policyOf smallHead)) (some scales) (some (some SmallFiles.layout))).toOption.bind
    fun l => l.lookup "entry"

/-- The digest of parameter bytes, in hexadecimal digits. -/
def bytesDigest (b : ByteArray) : String := Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm b)

/-- The scales with the lowest bit of their first byte turned. -/
def turnedScales : ByteArray :=
  SmallFiles.scales.set! 0 (SmallFiles.scales.get! 0 ^^^ 1)

-- cp_verify's line h_par= for these files
#guard (hPar (policyOf smallHead) SmallFiles.scales (some SmallFiles.layout)).toOption.map hex64 ==
  some "17698ba06ca1511ac8a068f42425b25b39929acad4dc627886c53309059f303b"
-- another file gives another digest
#guard (hPar (policyOf smallHead) turnedScales (some SmallFiles.layout)).toOption.map hex64 !=
  some "17698ba06ca1511ac8a068f42425b25b39929acad4dc627886c53309059f303b"
-- the command `plan` ends well, with the length and the digest that OnBytes/Params/TestDerive.lean
-- holds for the entry's chain
#guard (planEntryAt SmallFiles.scales).any fun b => b.size == 3154 &&
  bytesDigest b == "024a450069cd46ebdeb048d9ec5c3860e8eb16cb4be3a42c0d72f3c33e7ce6d7"
-- another file gives other bytes, or none
#guard (planEntryAt turnedScales).all fun b =>
  bytesDigest b != "024a450069cd46ebdeb048d9ec5c3860e8eb16cb4be3a42c0d72f3c33e7ce6d7"
-- a target above the files' own is refused
#guard (match planBytes 129 (some (policyOf smallHead)) (some SmallFiles.scales)
    (some (some SmallFiles.layout)) with
  | .error e => e == .no "security-bits"
  | .ok _ => false)

end OnBytes.Model.Verify.TestRecordWork
