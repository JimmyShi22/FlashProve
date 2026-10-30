-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullFw.lean: the first toy, the full parameters, files of this library's own: helpers for
the tests of the verifier on bytes on thirteen proof files. They give the outcome that the table of
bad files asks for, and the run on files by name.

The verifier on bytes is `whoF` (Fmt/M1Full.lean); that file's head says what its two stages, the
reader and the decision, are.

1. What the file contains. Three definitions. No Mathlib.
   `wantsF`: the outcome that the table asks for. Where the table names nothing, it is "accepted".
      Where the table names form, work or openings (its parts 1, 2, 3), it is "reader". Where the
      table names one of the last block's two checks (parts 4, 5), it is "decision".
   `atF names`: the files of these names in the table (Fmt/M1FilesF.lean: `files`, then `recut`),
      each with what the table says of it.
   `spokeF names`: for each of these files, its name, the outcome of the verifier on bytes (`whoF`,
      Fmt/M1Full.lean) at `KnownF.spec` and `KnownF.par`, and the outcome that the table asks for.
      The five files Fmt/M1FullFa.lean to Fmt/M1FullFe.lean call it.

2. What is checked when the file compiles. Two tests (#guard), on the description (`KnownF.spec`)
and the table alone. The first tests the sizes that the other heads name: 30 rounds; trees of depth
15, 14, 14; 73, 74, 74 positions; 20 bits of work. The second tests the table's thirteen rows, with
their sizes and the outcomes asked for.

3. Theorems. None.

Notation:
   a name bad-Dn, with or without letters after it, has the part dn beside it in the table;
   bad-D1b: the first word of the answer y is p;
   bad-D1ca, bad-D1cb, bad-D1cc: the first word of the first opened column of tree 0, 1, 2 is p
   (Fmt/M1FilesF.lean; p is `Fld.p`, Fmt/Rules1.lean);
   `.a`: a tree's depth (`Shape`, Fmt/Plan.lean).

4. What is not claimed. No outcome of the verifier on bytes (`whoF`) is tested in this file; see
Fmt/M1FullF.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Full
import Fmt.M1PlanKnownF

namespace Fmt.M1
namespace Full

def wantsF : Option FilesF.Dn → Tiny.Who
  | none => .accepted
  | some .d1 => .reader
  | some .d2 => .reader
  | some .d3 => .reader
  | some .d4 => .decision
  | some .d5 => .decision

/-- the files of these names -/
def atF (names : List String) : List (String × ByteArray × Option FilesF.Dn) :=
  (FilesF.files ++ FilesF.recut).filter fun x => names.contains x.1

/-- For each file of these names (`atF names`): its name, the outcome of `whoF` at `KnownF.spec` and
`KnownF.par`, and the outcome that the table asks for. -/
def spokeF (names : List String) : List (String × Tiny.Who × Tiny.Who) :=
  (atF names).map fun x => (x.1, whoF KnownF.spec KnownF.par x.2.1, wantsF x.2.2)

end Full

-- the sizes that the heads name
#guard KnownF.spec.rounds.length == 30 && (List.range 4).map (fun n => (KnownF.spec.shapeOf n).map (·.a)) == [some 15, some 14, some 14, none] &&
  (KnownF.spec.rounds.filter fun r => r.entry.poss != 0).map (fun r => (r.entry.poss, r.entry.work)) == [(73, 20), (74, 20), (74, 20)]
-- the table: thirteen files
#guard (FilesF.files ++ FilesF.recut).map (fun x => (x.1, x.2.1.size, Full.wantsF x.2.2)) ==
  [("honest", 161408, .accepted), ("bad-D1", 161407, .reader), ("bad-D1b", 161408, .reader), ("bad-D2", 161408, .reader), ("bad-D3", 161408, .reader), ("bad-D4", 161280, .decision), ("bad-D5", 161088, .decision),
   ("bad-D1ca", 161408, .reader), ("bad-D1cb", 161408, .reader), ("bad-D1cc", 161408, .reader), ("recut-24", 162016, .reader), ("recut-28", 160960, .reader), ("recut-30", 161504, .reader)]

end Fmt.M1
