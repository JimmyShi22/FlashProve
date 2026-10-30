-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1RunS.lean: the first toy at two tiny sizes of this library's own, through the compiled
verifier with the real hash: both honest files are accepted and all 71 bad files are refused, each
by the expected component.

Tests only. The first toy is a product test; its protocol is taken from the programs' description
of the toy (the programs: the C++ implementation that comes with this Lean code). (A product test:
on rows a, b, c with a_i b_i = c_i for every i; Fmt/M1Types.lean.) "The expected component" is the
file reader or the verifier, as the table that came with the files asks, behind both file readers.
(The table: for each bad file the part refusing first in the reference program's verifier; `files`,
Fmt/M1Files.lean, Fmt/M1FilesB.lean.) The count of 71 is not tested here: it follows from the tests
on `tally` in Run/M1Run.lean.

Sources. The files are this library's own. They were made outside Lean by a reference program of
this library's own, written from the programs' description of the toy, at sizes of this
library's own, at an edition of the format page that is not the one that ships
(docs/format/FORMAT.md; this file is not held against the page that ships).

1. What the file contains. No definition.
How a file is run (Run/PlanQS.lean: `runStrictS`, `runLaxS`):
   the file goes to a reader (the format page's own, or the lenient one, which only splits the
     file; to cut the file, the lenient reader recomputes the hash chain, and it refuses some files
     (what it still asks the hash, what it refuses and what it does not test: part 1 of the head of
     Run/ParseLax.lean));
   the reader returns the typed argument string;
   on it runs `VP`, which by Run/PlanQS.lean's theorem `vp_eq` is `Compile.Batch.verifyOneProtocol` at the
     protocol made from the description, run by `det` at the typed oracle functions that BLAKE2b on
     the format's strings induces.
The protocol's decision is `Fmt.M1.dec` on the untyped view.

2. What is checked when the file compiles.
   What is asked (Run/M1Run.lean: `wrong`, `wantStrict`, `wantLax`, from the table that came with
   the files).
     Behind the strict reader: form, work and openings are refused by the reader, the last block's
       two checks by the verifier.
     Behind the lenient reader the verifier itself must refuse a false opening.
   Named apart: alt-05 (a byte of a salt) and alt-06 (a byte of a given digest) at both sizes. By
   the tests in Run/M1Run.lean the decision alone accepts them behind the lenient reader. Here the
   verifier refuses them. So it is not the decision that refuses. Which of the verifier's other
   checks refuses, no test here shows; by the way these files were made (one byte of a salt, one
   byte of a given digest) it is the verifier's own walk through the openings.

3. Theorems. None. The tests are evaluations made when the file is compiled: they leave no theorem.

4. What is not claimed.
   No file of the programs is run here (see Sources).
   The runs are at typed oracle functions with the hash behind them, not over a single oracle
   through an encoding of the queries.
   No file here makes the verifier's own test of the work the one that refuses (see the head of
   Run/M1Run.lean).
   No statement on soundness follows.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQS
import Run.M1Run

namespace Run.M1RunS
open _root_.Fmt.M1 Run.PQ Run.M1Run

-- the honest files
#guard runLaxS Known.spec (dec Known.par) Files.honest = .accepted ∧ runStrictS Known.spec (dec Known.par) Files.honest = .accepted
#guard runLaxS KnownB.spec (dec KnownB.par) FilesB.honest = .accepted ∧ runStrictS KnownB.spec (dec KnownB.par) FilesB.honest = .accepted
-- every file, behind the lenient reader: the outcome is the one that the table asks for
#guard wrong runLaxS wantLax Known.spec Known.par filesA = []
#guard wrong runLaxS wantLax KnownB.spec KnownB.par filesB = []
-- every file, behind the page's own reader
#guard wrong runStrictS wantStrict Known.spec Known.par filesA = []
#guard wrong runStrictS wantStrict KnownB.spec KnownB.par filesB = []
-- alt-05, alt-06 at both sizes, which the decision alone accepts: here the verifier refuses them
#guard (filesA.filter fun x => x.1 == "alt-05" || x.1 == "alt-06").map (fun x => runLaxS Known.spec (dec Known.par) x.2.1) = [.verifier, .verifier]
#guard (filesB.filter fun x => x.1 == "alt-05" || x.1 == "alt-06").map (fun x => runLaxS KnownB.spec (dec KnownB.par) x.2.1) = [.verifier, .verifier]
-- one size's honest file under the other size's description
#guard runLaxS KnownB.spec (dec KnownB.par) Files.honest ≠ .accepted ∧ runLaxS Known.spec (dec Known.par) FilesB.honest ≠ .accepted
-- the decision bears on the verdict: with the decision "no" the honest file is refused by the
-- verifier; with "yes" a file of part 4 is accepted
#guard runLaxS Known.spec (fun _ => false) Files.honest = .verifier
#guard ((filesA.filter fun x => x.2.2 == 4).head?.map fun x => runLaxS Known.spec (fun _ => true) x.2.1) = some .accepted

end Run.M1RunS
