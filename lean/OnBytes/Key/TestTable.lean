-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Key/TestTable.lean: tests of OnBytes/Key/Table.lean.

Every test is checked when the file compiles. The program does not import this file.

Three more known answers, at a shape with a record, are lines of docs/format/format-vectors.txt. One
more, at rows of 100 entries, was computed by docs/format/format_rules.py and is on no list.
-/
import OnBytes.Key.Table

namespace OnBytes.Key.Test

open OnBytes.Params (TableName IndexShape)

/-- The tables' shape in these tests: 2 rows with a record of one answer each; words of length 2^23;
524288 entries in a row's message and 65535 in its random tail; 40 bytes of salt in a leaf. -/
def shape : IndexShape := { code := ⟨23, 524288, 65535⟩, v := 1, answers := 1, saltBytes := 40 }

/-- A digest of three public files. -/
def cfg : ByteArray :=
  Fmt.unhex "c128f3294c61acad20d5276d5f24c653975d8c24d0ec89700e9d7877d485ed13"

/-- A table's name: a root alone. -/
def table : TableName :=
  { root := Fmt.unhex "15e07de0498c4c9880f048609d3c74dd286c94dcc57a803b412f208e9684c12d" }

/-- The shape of the format page's three known answers for the commitment ID (R4.11). -/
def pageShape : IndexShape := { code := ⟨10, 512, 40⟩, v := 9, answers := 1, saltBytes := 40 }

/-- Their table with two answers. -/
def pageTable : TableName :=
  { root := Fmt.pattern 32 13 4, answers := [E.mk3 1 2 3, E.mk3 4 5 6] }

-- the format page's known answer with no seed and no answer
#guard Fmt.hex (commitmentIdAt pageShape Fmt.Toy4.cfg [] { root := Fmt.pattern 32 13 4 } []) ==
  "80d59c8b07aaa71829c9765057082a108618402daf661caf2c390c09dfafddd3"
-- with a given seed, a point of two coordinates and a factor, and two answers: the coding alone
#guard Fmt.hex (commitmentIdAt pageShape Fmt.Toy4.cfg [] pageTable
    [([E.mk3 7 8 9, E.mk3 10 11 12], E.mk3 13 14 15)]) ==
  "4fb918a30faa7643cf8e6bc431c6643d7b5b4cc298dd0531cc0206bb4f756a0b"
-- with the name's own seed, drawn and not given, and the same two answers
#guard Fmt.hex (commitmentId pageShape Fmt.Toy4.cfg pageTable) ==
  "e18438e0725ec651fc8bffa3b3f860ddeca70e6cb1991dd43620b98ef6f05bd2"
-- at rows of 100 entries the seed's point has 7 coordinates (100 ≤ 2^7), while the table still has
-- 2^9 rows: record_seeds(name, 7, 1, 2) of the format's own script; the second value is the
-- script's at 9 coordinates
#guard Fmt.hex (commitmentId { pageShape with code := ⟨10, 100, 40⟩ } Fmt.Toy4.cfg pageTable) ==
  "99b2bc80b559f9369395800784598e1c1442f76c1794ba9f1bb1a581001a9b6d"
#guard Fmt.hex (commitmentId { pageShape with code := ⟨10, 100, 40⟩ } Fmt.Toy4.cfg pageTable) !=
  "03d12190088869a78a9ab5459de2daf8da036f5126ce4a9f3466e72d102c1ce2"

/-- The first 40 bytes of the key file. -/
def beginning : ByteArray := Fmt.ascii "CPIKH821" ++ table.root

/-- The stage and the name under which a reading was refused; nothing if it was not refused. -/
def refusal (x : Except Refusal (TableName × Nat)) : Option (Stage × String) :=
  match x with
  | .error e => some (e.stage, e.check)
  | .ok _ => none

-- refused: a file of another kind; another version; a root that is cut short
#guard refusal (readTable shape cfg (Fmt.ascii "CPENH821" ++ table.root)) ==
  some (.key, "file-of-another-kind")
#guard refusal (readTable shape cfg (Fmt.ascii "CPIKH811" ++ table.root)) ==
  some (.key, "version-of-another-field")
#guard refusal (readTable shape cfg (beginning.extract 0 39)) == some (.key, "root")
-- refused: a shape that no table may have
#guard refusal (readTable { shape with v := 41 } cfg beginning) ==
  some (.configuration, "table-shape")
#guard refusal (readTable { shape with saltBytes := 39 } cfg beginning) ==
  some (.configuration, "table-shape")
-- with a record of one answer for each of two rows, the answers are read
#guard ((readTable { shape with v := 1, answers := 1 } cfg
    (beginning ++ Fmt.ext (1, 2, 3) ++ Fmt.ext (4, 5, 6))).toOption.map
      fun x => (x.1.answers, x.2)) == some ([E.mk3 1 2 3, E.mk3 4 5 6], 88)
-- refused: 32 zero bytes as the digest of the public files: the file is whole
#guard refusal (readTable { shape with v := 1, answers := 1 } Fmt.zero32
    (beginning ++ Fmt.ext (1, 2, 3) ++ Fmt.ext (4, 5, 6))) == some (.key, "table")
-- refused: an answer is missing; a coordinate is not below the prime
#guard refusal (readTable { shape with v := 1, answers := 1 } cfg
    (beginning ++ Fmt.ext (1, 2, 3))) == some (.key, "record-answers")
#guard refusal (readTable { shape with v := 1, answers := 1 } cfg
    (beginning ++ Fmt.ext (1, 2, 3) ++ Fmt.ext (4, 5, 18446744069414584321))) ==
  some (.key, "record-answers")

end OnBytes.Key.Test
