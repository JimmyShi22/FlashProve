-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1RunF.lean: the first toy at the programs' full parameters (the toy's full sizes), on files of
this library's own, through the compiled verifier with the real hash: one proof is accepted and
twelve bad files are refused, six of them by the verifier itself behind the lenient reader.

The first toy is a product test. The programs are the C++ implementation that comes with this Lean
code. This file holds three small definitions and tests. The run functions are `runStrictS` and
`runLaxS` (Run/PlanQS.lean). What runs behind the file reader is `Compile.Batch.verifyOneProtocol`, run by
`det` at typed oracle functions with BLAKE2b behind them (`vp_eq` in Run/PlanQS.lean). The decision
is `Fmt.M1.dec`. What is asked comes from Run/M1Run.lean (`wrong`, `wantStrict`, `wantLax`) and
from the table that came with the files (for each bad file the part refusing first in the reference
program's verifier; `files`, `recut`, Fmt/M1FilesF.lean).

Sources. The files (Fmt/M1FilesF.lean; the description: Fmt/M1PlanKnownF.lean) were made anew at an
edition of the page, not in this repository (docs/format/FORMAT.md; not held against the page that
ships): 30 rounds; trees of depth 15, 14, 14. The parameter bytes were spelled by a reading of that
edition, which leaves open whether they are the programs' bytes. A test in Fmt/M1PlanKnownF.lean
compares them, and the public file, with the programs' own (Fmt/M1Theirs.lean): they are equal. The
proofs are this library's own, made by a reference program of this library's own (outside Lean).

1. What the file contains. The list of files: one honest file of some 161,000 bytes, nine bad ones
with the part of the decision that refuses first, and three re-cut files (a nonce that fails the
test of the work at one of the three rounds with work; all that follows by the honest rules).

2. What is checked when the file compiles. The honest file is accepted behind both readers. On
every file the outcome is the one that the table asks for, behind both readers. The three re-cut
files: behind the lenient reader the verifier refuses, and the lenient reader with the decision
alone accepts. So it is not the decision that refuses. Which of the verifier's other checks
refuses, no test here shows; by the way these files were made (all honest behind a failing nonce)
it is the verifier's own test of the work.

3. Theorems. None. The tests are evaluations made when the file is compiled: they leave no theorem.

4. What is not claimed.
   No proof file of the programs is run here.
   The runs are at typed oracle functions, not over a single oracle through an encoding of the
   queries.
   No statement on soundness follows.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQS
import Run.M1Run
import Fmt.M1PlanKnownF
import Run.ParseLaxFast

namespace Run.M1RunF
open _root_.Fmt.M1 Run.PQ Run.M1Run

def partF : Option FilesF.Dn → Nat
  | none => 0
  | some .d1 => 1
  | some .d2 => 2
  | some .d3 => 3
  | some .d4 => 4
  | some .d5 => 5

/-- all files, the re-cut ones behind the others: name, bytes, the table's part -/
def filesF : List (String × ByteArray × Nat) :=
  (FilesF.files ++ FilesF.recut).map fun x => (x.1, x.2.1, partF x.2.2)

/-- the lenient reader (in its fast form, which is proved to be the reader), then the decision on
the view: no compiled verifier -/
def bareLaxF : Runner := fun S d b =>
  match laxWholeF S b with
  | none => .reader
  | some o => if d (_root_.Fmt.viewOf S.firstTree o) then .accepted else .verifier

#guard (rds KnownF.spec).length = 30 ∧ ((rds KnownF.spec).filterMap fun d => d.tree.map (·.a)) = [15, 14, 14]
#guard filesF.map (fun x => (x.1, x.2.2)) = [("honest", 0), ("bad-D1", 1), ("bad-D1b", 1), ("bad-D2", 2), ("bad-D3", 3), ("bad-D4", 4), ("bad-D5", 5), ("bad-D1ca", 1), ("bad-D1cb", 1), ("bad-D1cc", 1), ("recut-24", 2), ("recut-28", 2), ("recut-30", 2)]
-- the honest file
#guard runLaxS KnownF.spec (dec KnownF.par) FilesF.honest = .accepted
#guard runStrictS KnownF.spec (dec KnownF.par) FilesF.honest = .accepted
-- every file: the outcome is the one that the table asks for
#guard wrong runLaxS wantLax KnownF.spec KnownF.par filesF = []
#guard wrong runStrictS wantStrict KnownF.spec KnownF.par filesF = []
-- behind the lenient reader the verifier itself is to refuse six files
#guard (filesF.filter fun x => wantLax x.1 x.2.2 = .verifier).length = 6
-- the three re-cut files: the verifier refuses; the decision alone accepts
#guard FilesF.recut.map (fun x => (runLaxS KnownF.spec (dec KnownF.par) x.2.1, bareLaxF KnownF.spec (dec KnownF.par) x.2.1)) = [(.verifier, .accepted), (.verifier, .accepted), (.verifier, .accepted)]

end Run.M1RunF
