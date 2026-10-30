-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1RunT.lean: the first toy at the programs' tiny parameters, on files of this library's own,
through the compiled verifier with the real hash; and files that were made so that, behind the
lenient reader, only the verifier's own test of the proof of work refuses them.

The first toy is a product test. The programs are the C++ implementation that comes with this Lean
code. This file holds six small definitions and tests. The run functions are `runStrictS` and
`runLaxS` (Run/PlanQS.lean). What runs behind the file reader is `Compile.Batch.verifyOneProtocol`, run by
`det` at typed oracle functions with BLAKE2b behind them (`vp_eq` in Run/PlanQS.lean). The decision
is `Fmt.M1.dec`.

Sources. The sets of files T and R (Fmt/M1FilesT.lean, Fmt/M1FilesR.lean) were made anew at an
edition of the format page that is not the one that ships (docs/format/FORMAT.md; this file is not
held against the page that ships). The sizes are those of the programs' tiny parameters (22 rounds;
trees of depth 7, 8, 9: tested here at the description of set R). The parameter bytes were spelled
by a reading of that edition, which leaves open whether they are the programs' bytes. Tests in
Fmt/M1PlanKnownT.lean and Fmt/M1PlanKnownR.lean compare them, and the public file, with the
programs' own (Fmt/M1Theirs.lean): they are equal. Everything else in the files is this library's
own: witness, coins and all messages come from a reference program of this library's own (outside
Lean), but for the chain's random bytes in set R's files, which are taken from a run of the programs
(Fmt/M1FilesR.lean).

1. What the file contains.
   The lists `filesT`, `filesR`. In each set: the honest file, the bad files with the part of the
   decision that refuses first, and three re-cut files. A re-cut file has, at one of the three
   rounds with work, a nonce that fails the test, and all that follows is made by the honest rules
   at what that nonce draws. By its own assertion this library's own reference refuses them for the
   work, and accepts them with its test of the work switched off. The re-cut files of the two sizes
   of this
   library's own (Fmt/M1Files.lean, Fmt/M1FilesB.lean) are run here too.
   `luckT`, `luckR`: three files fixed by name. In each a byte in front of a round with work is
     altered, and which component refuses behind the lenient reader depends on what is then drawn
     (see the head of Run/M1Run.lean).
   What is asked comes from Run/M1Run.lean (`wrong`, `wantStrict`, `wantLaxAt`) and from the tables
   that came with the files.

2. What is checked when the file compiles.
   At T and at R the honest file is accepted behind both readers. On every file, the re-cut ones
   among them, the outcome is the one that the table asks for, behind both readers, except for the
   three files fixed by name behind the lenient reader (T: alt-01, alt-03: the verifier where the
   rule has the reader; R: alt-01: the reader where the rule has the verifier). These three are
   refused all the same.
   All twelve re-cut files: behind the lenient reader the verifier refuses. The lenient reader with
   the decision alone (no compiled verifier) accepts all twelve. So it is not the decision that
   refuses. Which of the verifier's other checks refuses, no test here shows; by the way these
   files were made (all honest behind a failing nonce, by the reference's own assertion) it is the
   verifier's own test of the work.

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
import Fmt.M1PlanKnownT
import Fmt.M1PlanKnownR

namespace Run.M1RunT
open _root_.Fmt.M1 Run.PQ Run.M1Run

def partT : Option FilesT.Dn → Nat
  | none => 0
  | some .d1 => 1
  | some .d2 => 2
  | some .d3 => 3
  | some .d4 => 4
  | some .d5 => 5

def partR : Option FilesR.Dn → Nat
  | none => 0
  | some .d1 => 1
  | some .d2 => 2
  | some .d3 => 3
  | some .d4 => 4
  | some .d5 => 5

/-- all files of a set, the re-cut ones behind the others: name, bytes, the table's part -/
def filesT : List (String × ByteArray × Nat) :=
  (FilesT.files ++ FilesT.recut).map fun x => (x.1, x.2.1, partT x.2.2)
def filesR : List (String × ByteArray × Nat) :=
  (FilesR.files ++ FilesR.recut).map fun x => (x.1, x.2.1, partR x.2.2)

/-- the files whose outcome behind a lenient reader depends on the draws (Run/M1Run.lean:
`wantLaxAt`), as the runs below have it -/
def luckT : List (String × Who) := [("alt-01", .verifier), ("alt-03", .verifier)]
def luckR : List (String × Who) := [("alt-01", .reader)]

#guard luckOK luckT filesT ∧ luckOK luckR filesR
-- how many files, part by part; the names of the re-cut ones
#guard (List.range 6).map (fun d => (filesT.filter fun x => x.2.2 == d).length) = [1, 6, 6, 4, 23, 6]
#guard (List.range 6).map (fun d => (filesR.filter fun x => x.2.2 == d).length) = [1, 6, 5, 5, 23, 6]
#guard (filesR.filter fun x => x.1.startsWith "recut").map (fun x => (x.1, x.2.2)) = [("recut-16", 2), ("recut-20", 2), ("recut-22", 2)]
#guard (rds KnownR.spec).length = 22 ∧ ((rds KnownR.spec).filterMap fun d => d.tree.map (·.a)) = [7, 8, 9]
-- the honest files
#guard runLaxS KnownR.spec (dec KnownR.par) FilesR.honest = .accepted ∧ runStrictS KnownR.spec (dec KnownR.par) FilesR.honest = .accepted
#guard runLaxS KnownT.spec (dec KnownT.par) FilesT.honest = .accepted ∧ runStrictS KnownT.spec (dec KnownT.par) FilesT.honest = .accepted
-- every file, behind the lenient reader and behind the page's own: the outcome is the one that the
-- table asks for, but, behind the lenient reader, for the files of `luckT`, `luckR`
#guard wrong runLaxS (wantLaxAt luckR) KnownR.spec KnownR.par filesR = []
#guard wrong runStrictS wantStrict KnownR.spec KnownR.par filesR = []
#guard wrong runLaxS (wantLaxAt luckT) KnownT.spec KnownT.par filesT = []
#guard wrong runStrictS wantStrict KnownT.spec KnownT.par filesT = []
-- the twelve re-cut files: the verifier refuses; the decision alone accepts
#guard FilesR.recut.map (fun x => (runLaxS KnownR.spec (dec KnownR.par) x.2.1, bareLax KnownR.spec (dec KnownR.par) x.2.1)) = [(.verifier, .accepted), (.verifier, .accepted), (.verifier, .accepted)]
#guard FilesT.recut.map (fun x => (runLaxS KnownT.spec (dec KnownT.par) x.2.1, bareLax KnownT.spec (dec KnownT.par) x.2.1)) = [(.verifier, .accepted), (.verifier, .accepted), (.verifier, .accepted)]
#guard Files.recut.map (fun x => (runLaxS Known.spec (dec Known.par) x.2.1, bareLax Known.spec (dec Known.par) x.2.1)) = [(.verifier, .accepted), (.verifier, .accepted), (.verifier, .accepted)]
#guard FilesB.recut.map (fun x => (runLaxS KnownB.spec (dec KnownB.par) x.2.1, bareLax KnownB.spec (dec KnownB.par) x.2.1)) = [(.verifier, .accepted), (.verifier, .accepted), (.verifier, .accepted)]
-- behind the page's own reader the reader refuses the three of set R
#guard (FilesR.recut.map fun x => runStrictS KnownR.spec (dec KnownR.par) x.2.1) = [.reader, .reader, .reader]

end Run.M1RunT
