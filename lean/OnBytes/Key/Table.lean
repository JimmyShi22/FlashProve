-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Key/Table.lean: the table that a key file names, and the commitment ID.

A key file begins with its head, the root of the first stored table and the answers of the table's
record (docs/format/FORMAT.md, R13.1 and R13.2). This file reads that beginning and tests its
form. It reads none of the key's proofs.

Words. A stored table is a committed table: 2^v rows over the base field under the root of one hash
tree, made once and read by many runs. It holds the committed matrix (OnBytes/Key/File.lean). For
each row the committer may store answers to the table's own sample, elements of the extension field;
the stored answers of all rows are the table's record (`IndexShape`, OnBytes/Params/Items.lean). The
public files are the configuration's; every reader computes their digest itself (R4.9).

A yes of `Key.readTable` says that these bytes have the form of a key's beginning, and nothing about
the table. The check of the whole file (OnBytes/Key/File.lean) begins with this reading. Whoever
else takes a table from here has checked none of the key's proofs: it relies on a check of the whole
file on the same bytes.

The table's name (R4.10) is its root, the digest of the public files and six words of its shape.
The commitment ID (R4.11) is one hash of the digest of the public files, the name, the record's
seeds, the record's answers and a closing list, which is empty: the format defines no element of it.
Nothing of the key's proofs enters it.

Main definitions: `Key.tableOk`, `Key.readTable`, `Key.nameOf`, `Key.seedsOf`,
`Key.commitmentIdAt`, `Key.commitmentId`.
C++ counterpart: read_key_table_unproved() in blocks/frame/check_key.h; index_key_fault() in
blocks/iop/foldeq.h.
-/
import OnBytes.Iop.Foldeq
import OnBytes.Params.Chains
import OnBytes.Entry.Table
import OnBytes.Proof.Head
import OnBytes.Result

namespace OnBytes.Key

open OnBytes.Params (TableName IndexShape)

/-- A refusal in the stage of the key file. -/
def no {α : Type} (check : String) : Except Refusal α := .error ⟨.key, check⟩

/-- The table that a file names has an admitted form: the shape passes `IndexShape.ok`; the digest
of the public files is not 32 zero bytes; the record has `s.answers` answers for each row. -/
def tableOk (s : IndexShape) (cfg : ByteArray) (t : TableName) : Bool :=
  s.ok && cfg != Fmt.zero32 && t.answers.length == s.rows * s.answers

/-- Reads the beginning of a key file: head, root, the record's answers. s is the tables' shape and
cfg the digest of the public files; both are the reader's own and never the file's. Returns the
table and the place of the first byte after the answers, or the first check that failed. The shape
is tested before a byte is read, since the number of answers follows from it. `.two` is the one of
the format's two fields in which this program computes. -/
def readTable (s : IndexShape) (cfg file : ByteArray) : Except Refusal (TableName × Nat) :=
  if !s.ok then .error ⟨.configuration, "table-shape"⟩
  else
    match Proof.readHead .two .key file with
    | .error e => no e
    | .ok i =>
      match OnBytes.readTable .two (s.rows * s.answers) file i with
      | .error e => no e
      | .ok (table, j) => if tableOk s cfg table then .ok (table, j) else no "table"

/-- The table's name (R4.10): 112 bytes. It is in no file and in no item of a file's chains. It is
the statement of the chain from which the record's seeds are drawn (R4.8), and it enters the
commitment ID (R4.11). -/
def nameOf (s : IndexShape) (cfg : ByteArray) (t : TableName) : ByteArray :=
  Fmt.tableName t.root cfg s.code.logN s.code.ell s.code.r s.v s.answers s.saltBytes

/-- The seeds of the table's record (R4.8). s is the tables' shape, cfg the digest of the public
files, t the table. The seeds are drawn from the table's name. Returns nothing if the drawing fails.
This is the first step of `tableKey` (OnBytes/Entry/Table.lean), with `.two` for its field. -/
def seedsOf (s : IndexShape) (cfg : ByteArray) (t : TableName) : Option (List (List E × E)) :=
  recordSeeds .two (nameOf s cfg t) s.cubeBits s.answers

/-- `tableKey` at the field `.two` draws these seeds, then builds the key from them. -/
theorem tableKey_seedsOf (s : IndexShape) (cfg : ByteArray) (t : TableName) (item : Nat) :
    tableKey .two cfg s t item = (seedsOf s cfg t).bind fun seeds =>
      let key : TableKey :=
        { item := item, record := t.answers.toArray, seeds := seeds.map fun x => ⟨x.1, x.2⟩ }
      if key.fits s then some key else none := by
  unfold tableKey seedsOf nameOf
  rfl

/-- The commitment ID (R4.11) at given seeds: 32 bytes. told is the closing list: the format leaves
it empty, and `commitmentId` passes the empty list. The seeds enter as one flat list: seed by seed,
the coordinates of its point and then its factor. One call of the hash; no seed is drawn here. -/
def commitmentIdAt (s : IndexShape) (cfg : ByteArray) (told : List ByteArray) (t : TableName)
    (seeds : List (List E × E)) : ByteArray :=
  Fmt.publishedID cfg (nameOf s cfg t) ((seeds.flatMap fun y => y.1 ++ [y.2]).map E.triple)
    (t.answers.map E.triple) told

/-- The commitment ID: 32 bytes. It draws the record's seeds itself (`seedsOf`) and lays the empty
closing list: the string ends in the word 0. If `seedsOf` returns nothing, the empty list stands in
the seeds' place. In the C++ verifier the drawing cannot fail (record_seeds() in
blocks/chain/rounds.h). -/
def commitmentId (s : IndexShape) (cfg : ByteArray) (t : TableName) : ByteArray :=
  commitmentIdAt s cfg [] t ((seedsOf s cfg t).getD [])

end OnBytes.Key
