-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/Table.lean: how a stored table's root and answers are read from a file.

A stored table is a committed matrix of weights. The first stored table comes with a key file. A
further stored copy of the same rows comes with an entry file. A table may have a record: for each
row, the row's answers to a sample whose seeds are drawn from the table's name (R4.8, R13.8). In
both files the table's root and the record's answers, if tables have a record, follow the head
directly (docs/format/FORMAT.md, R13.2, R13.3). These are all that a reader keeps of a table
(`Params.TableName`), and the statements of a later proof hold them by value (R4.6).

Two things have similar names. The type `Params.TableName` is the root with the answers. The
format's name of a table (R4.10; `Fmt.tableName`) is the root, the digest of the public files and
the six words of the tables' shape. In this file's text "the table's name" is always the second.
C++: read_key_table_unproved (blocks/frame/check_key.h) and read_entry_table_unproved
(blocks/frame/check_entry.h). Both also read the head and ask index_key_fault; `readTable` does not.

Main definitions: `readTable`, `recordSeeds`, `tableKey`.

What is not claimed: a value of the type `Params.TableName` says nothing about the table. Whether
a key file or an entry file has been checked is up to whoever made the value.
-/
import OnBytes.Params.Chains
import OnBytes.Iop.Foldeq
import OnBytes.Chain.Loops
import OnBytes.Chain.Draws
import Fmt.Rules5
import Fmt.Rules6Round

namespace OnBytes

/-- Reads a root and `count` answers at byte i of b. Each answer must be in canonical form. Returns
the root with the answers and the place after them, or the name of the test that failed. -/
def readTable (f : Fmt.Fld) (count : Nat) (b : ByteArray) (i : Nat) :
    Except String (Params.TableName × Nat) :=
  match Fmt.rdDigest b i with
  | none => .error "root"
  | some (root, j) =>
    match rdManyT (Fmt.rdExt f) count b j with
    | none => .error "record-answers"
    | some (ys, k) => .ok (⟨root, ys.map E.ofTriple⟩, k)

/-- The names under which `readTable` refuses. -/
def tableNames : List String := ["root", "record-answers"]

/-- The seeds of a stored table's record (R4.8): `count` seeds, each a point of `bits` coordinates
and a factor that is not 0. They are drawn from a chain of their own, which starts from the table's
name (R4.10) and nothing else and has one round, in which the prover says nothing. A seed uses at
most 18 words of that round's answer for each coordinate and 36 for its factor (R6.11). The seeds
are drawn by the loop `timesT`, which draws what `Fmt.Dr.times` draws (`timesT_eq`). -/
def recordSeeds (f : Fmt.Fld) (name : ByteArray) (bits count : Nat) :
    Option (List (List E × E)) :=
  match (⟨Fmt.recordLabel, Fmt.recordFirst name, 0⟩ : Fmt.Chain).query ByteArray.empty .seeds 0 0
      (Fmt.blocksFor (count * (bits * 18 + 36))) with
  | none => none
  | some (_, vb) =>
    some ((timesT (Fmt.drawSeed f bits) count (Fmt.rowOf vb) 0).1.map fun x =>
      (x.1.map E.ofTriple, E.ofTriple x.2))

/-- The table as the protocol's blocks read it (`TableKey`, OnBytes/Iop/Foldeq.lean; no key file),
from a table's root and answers. `item` is the number of the statement's item that holds the table.
The seeds of the table's record are a function of the table's name (R4.8, R4.10), which takes in the
root, the digest of the public files and the tables' shape. Returns nothing if the number of answers
is not the one that the shape says. -/
def tableKey (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape) (table : Params.TableName)
    (item : Nat) : Option TableKey := do
  let seeds ←
    recordSeeds f
      (Fmt.tableName table.root cfg s.code.logN s.code.ell s.code.r s.v s.answers s.saltBytes)
      s.cubeBits s.answers
  let key : TableKey :=
    { item := item, record := table.answers.toArray, seeds := seeds.map fun x => ⟨x.1, x.2⟩ }
  if key.fits s then some key else none

end OnBytes
