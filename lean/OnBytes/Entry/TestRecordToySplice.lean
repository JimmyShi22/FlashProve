-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/TestRecordToySplice.lean: Entry.check on the toy entry file of
OnBytes/Entry/RecordToyFiles.lean with bytes of one opening laid into another, and on the honest
file under a first table whose record is another.

1. Where the two stored tables' openings lie. The round LINK opens the first table and then the copy
   (R13.10, R8.7). Its first opening begins at byte 352: the head 8, the copy's root 32, its eight
   answers 192 (R13.3), the chain's random bytes 32, the root of SEND seed 32, the two answers of
   SEND answer 48, LINK's nonce 8 (R13.10, R8.2). An opening of m columns with g given digests has
   m (8 W + s) + 32 g bytes (R7.8), here with W = 8 and s = 40. m and g follow from the draws and
   are taken from what the strict reader (OnBytes/Iop/Ground.lean) has returned; the test holds the
   places that it returns against these sums. Within an opening a column is followed by its salt,
   leaf after leaf (R7.8): the first column of the first table's opening and the first two leaves
   of the copy's, cut out of the file at these places, are the columns and salts that the reader
   has returned.
2. Splices in the honest bytes, each refused under the name of an opening. In the copy's opening the
   first column is replaced by the first column of the first table's opening; the same with the
   column's salt; the copy's first two columns, with their salts, in each other's places.
3. The two openings in each other's places, as blocks of bytes, are the stored file bentSwap of
   Fmt/MustBeRefused/RecordToy.lean, byte for byte, as its docstring says.
4. The honest entry file under the first table's right root and another record. One answer replaced
   by its neighbour, and two answers in each other's places: refused under the name of a proof of
   work. An answer less, and one more: refused before the chain is read.

Where the expected endings come from. 2: a leaf's digest takes in the column and the salt (R7.3,
R7.4), and a verifier rejects an opening whose walk does not end in the tree's root (R7.10). 4: the
first table's answers stand in the statement (R13.5), which enters the chain's first value (R4.6),
so every later value moves, and the first thing that is tested on them is the work of LINK (R5.5),
eight bits; a changed chain passes it by luck once in 256. Before it reads the chain, a
verifier rejects if what it has kept of the first table has not one stored answer for each row and
seed (R13.10); the name of that refusal is read off Entry.read (OnBytes/Entry/File.lean).

Every test is checked when the file compiles. The program verify-on-bytes does not import this file.

Not claimed. No theorem. The splices and the changed records are made here from honest bytes; no
hash is made anew, so none of them is an attempt that a cheating prover would make.
An ending's name tells the kind of check and not which opening or which work has refused, and it
comes from a second pass over the file, of which OnBytes/Chain/Why.lean does not claim that it names
the reader's first failing step. So test 2 does not see where the bytes were laid: bytes changed
anywhere within the openings end alike, and for the function under test the three splices are one
case: a changed leaf under the copy's root. That the ranges are the leaves' is held by test 1.
No splice here holds that a leaf's position enters its digest: with two leaves in each other's
places the walk makes other parents whether or not it does.
Not tried: an entry under the first table of another key file that the programs have made from the
same public files; a file that lies about a record with its hashes made anew.
Nothing on soundness, completeness or hiding.
-/
import OnBytes.Entry.TestRecordToy

namespace OnBytes.Entry.RecordToySplice
open OnBytes.Entry.RecordToy (entryFile entryParameters firstTable ending)

/-- The place of the first byte behind LINK's nonce. -/
def opensAt : Nat := 8 + 32 + 8 * 24 + 32 + 32 + 2 * 24 + 8

/-- The bytes of a column of a stored table: eight elements of F. -/
def columnBytes : Nat := 8 * 8
/-- A column with its salt. -/
def leafBytes : Nat := columnBytes + 40

/-- The openings of the first round that has one, as the strict reader has returned them on the
honest file: for each the number of columns, the number of given digests, and the place behind
it. -/
def linkOpens : Option (List (Nat × Nat × Nat)) := do
  let p ← Params.Link.read entryParameters
  let t ← firstTable
  let r ← (Entry.read p t entryFile).toOption
  let x ← (r.chain.out.rounds.toList.filter fun x => !x.opens.isEmpty).head?
  pure (x.opens.map fun o => (o.2.2.cols.length, o.2.2.given.length, o.2.2.next))

/-- The first n leaves of opening number i of that round, as the strict reader has returned them:
each column's bytes and its salt. -/
def leavesOf (i n : Nat) : Option (List (ByteArray × ByteArray)) := do
  let p ← Params.Link.read entryParameters
  let t ← firstTable
  let r ← (Entry.read p t entryFile).toOption
  let x ← (r.chain.out.rounds.toList.filter fun x => !x.opens.isEmpty).head?
  let o ← x.opens[i]?
  pure (((o.2.2.cols.zip o.2.2.salts).take n).map fun c => (Fmt.colBytes c.1, c.2))

/-- The n leaves that lie in the file from byte a on: 64 bytes of a column, 40 of its salt. -/
def leavesAt (a n : Nat) : List (ByteArray × ByteArray) :=
  (List.range n).map fun j =>
    (entryFile.extract (a + j * leafBytes) (a + j * leafBytes + columnBytes),
      entryFile.extract (a + j * leafBytes + columnBytes) (a + (j + 1) * leafBytes))

/-- Where the copy's opening begins and ends, by the sums of R7.8. -/
def copyOpening : Option (Nat × Nat) :=
  match linkOpens with
  | some [(m0, g0, _), (m1, g1, _)] =>
    let a := opensAt + m0 * leafBytes + 32 * g0
    some (a, a + m1 * leafBytes + 32 * g1)
  | _ => none

/-- b with the n bytes at "to" replaced by the n bytes at "src". -/
def laid (b : ByteArray) (to src n : Nat) : ByteArray :=
  b.extract 0 to ++ b.extract src (src + n) ++ b.extract (to + n) b.size

/-- The splices: name and bytes. -/
def splices : Option (List (String × ByteArray)) := copyOpening.map fun c =>
  [("the copy's first column is the first table's", laid entryFile c.1 opensAt columnBytes),
   ("the copy's first column and its salt are the first table's",
      laid entryFile c.1 opensAt leafBytes),
   ("the copy's first two columns, with their salts, in each other's places",
      entryFile.extract 0 c.1 ++ entryFile.extract (c.1 + leafBytes) (c.1 + 2 * leafBytes) ++
        entryFile.extract c.1 (c.1 + leafBytes) ++
        entryFile.extract (c.1 + 2 * leafBytes) entryFile.size)]

/-- How Entry.check ends on the honest file under the first table t. -/
def endingUnder (t : Params.TableName) : String :=
  match Entry.check entryParameters t entryFile with
  | .ok _ => "yes"
  | .error r => r.check

/-- One answer replaced by its neighbour. -/
def replaced (l : List E) : List E := l.take 1 ++ l.take 1 ++ l.drop 2
/-- The first two answers in each other's places. -/
def exchanged (l : List E) : List E := (l.drop 1).take 1 ++ l.take 1 ++ l.drop 2

/-- The first table with its answers changed by g. -/
def otherRecord (g : List E → List E) : Option Params.TableName :=
  firstTable.map fun t => { t with answers := g t.answers }

-- 1. two openings, each of at least two columns and at most as many as its table has draws (R6.6):
-- members 2 and 3 of the list of the item "the link" (R13.9), 76 each; the places that the reader
-- returns are the sums; the leaves at these places are the reader's
#guard opensAt == 352
#guard ((Params.Link.read entryParameters).map fun p =>
  [p.link.columnsFirst, p.link.columnsFurther]) == some [76, 76]
#guard (linkOpens.map fun l => l.map fun o => decide (2 ≤ o.1) && decide (o.1 ≤ 76)) ==
  some [true, true]
#guard (linkOpens.bind fun l => copyOpening.map fun c => l.map (·.2.2) == [c.1, c.2]) == some true
#guard leavesOf 0 1 == some (leavesAt opensAt 1) &&
  (copyOpening.map fun c => leavesOf 1 2 == some (leavesAt c.1 2)) == some true
-- 2. the splices: as long as the file, other bytes, refused at an opening
#guard (splices.map fun l => l.map fun s =>
  (s.2.size == entryFile.size, s.2 != entryFile, ending s.2)) ==
  some (List.replicate 3 (true, true, some "reader-opening"))
-- 3. the two openings in each other's places
#guard (copyOpening.map fun c =>
  entryFile.extract 0 opensAt ++ entryFile.extract c.1 c.2 ++ entryFile.extract opensAt c.1 ++
    entryFile.extract c.2 entryFile.size == Fmt.MustBeRefused.RecordToy.bentSwap) == some true
-- 4. the record that the key file holds: yes; the first two answers differ
#guard (firstTable.map endingUnder) == some "yes"
#guard (firstTable.map fun t => t.answers.length == 8 && t.answers[0]? != t.answers[1]?) ==
  some true
#guard ((otherRecord replaced).map endingUnder) == some "reader-work"
#guard ((otherRecord exchanged).map endingUnder) == some "reader-work"
#guard ((otherRecord fun l => l.drop 1).map endingUnder) == some "table-record"
#guard ((otherRecord fun l => l ++ l.take 1).map endingUnder) == some "table-record"

end OnBytes.Entry.RecordToySplice
