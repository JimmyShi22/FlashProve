-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/TestTable.lean: tests of OnBytes/Entry/Table.lean.

`recordSeeds` gives the format page's known answer (docs/format/format-vectors.txt) and, at
other names and sizes, what the definition in Fmt/Rules56Known.lean gives. That definition is the
same formula with another loop, so the second comparison tests the loop and the conversion of
elements, and nothing else. The seeds of `tableKey` are compared with those of the table's name as
OnBytes/Key/Table.lean forms it, its record and item with the inputs. `readTable` is tried through
`Key.readTable` in OnBytes/Key/TestTable.lean. The program does not import this file.
-/
import OnBytes.Key.Table
import Fmt.Rules56Known

namespace OnBytes.TestTable

/-- Seeds as triples of words. -/
def plain (x : Option (List (List E × E))) :
    Option (List (List (UInt64 × UInt64 × UInt64) × (UInt64 × UInt64 × UInt64))) :=
  x.map (·.map fun s => (s.1.map E.triple, s.2.triple))

-- the format page's known answer: one seed with a point of two coordinates
#guard
  plain (recordSeeds .two (Fmt.tableName (Fmt.pattern 32 13 4) Fmt.Toy4.cfg 10 3 40 9 1 40) 2 1) ==
    some [([(9697749137137958355, 613613959841214928, 8403959380172774020),
             (15526148976690303146, 2032215208828410348, 4053187377642565227)],
            (14917727018641805655, 3966560771581124203, 17230899846445233913))]

/-- A made-up name of a table. -/
def someName (a : Nat) : ByteArray :=
  Fmt.tableName (Fmt.pattern 32 13 a) (Fmt.pattern 32 5 a) 10 3 40 9 1 40

#guard (List.range 4).all fun a =>
  [(0, 1), (2, 1), (5, 2), (12, 3)].all fun x =>
    plain (recordSeeds .two (someName a) x.1 x.2) ==
      Fmt.Known56.recordSeeds .two (someName a) x.1 x.2

/-- A shape with a record of one answer for each of four rows. Its six words all differ. -/
def shape : Params.IndexShape := ⟨⟨4, 8, 3⟩, 2, 1, 40⟩
/-- A made-up digest of public files. -/
def cfg : ByteArray := Fmt.pattern 32 5 2
/-- A made-up table with four answers. -/
def table : Params.TableName :=
  ⟨Fmt.pattern 32 13 7, [E.mk3 1 2 3, E.mk3 4 5 6, E.mk3 7 8 9, E.mk3 10 11 12]⟩

-- the seeds are those of the table's name; the answers keep their order; the item is the caller's
#guard ((tableKey .two cfg shape table 3).map fun k => k.seeds.map fun s => (s.z, s.beta)) ==
  recordSeeds .two (Key.nameOf shape cfg table) shape.cubeBits shape.answers
#guard ((tableKey .two cfg shape table 3).map fun k => (k.record.toList, k.item)) ==
  some (table.answers, 3)
-- three answers and five answers where four are due
#guard (tableKey .two cfg shape { table with answers := table.answers.dropLast } 3).isNone
#guard (tableKey .two cfg shape { table with answers := table.answers ++ [E.mk3 7 8 9] } 3).isNone
#guard (tableKey .two cfg shape table 3).isSome

end OnBytes.TestTable
