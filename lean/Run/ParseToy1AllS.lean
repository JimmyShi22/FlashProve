-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseToy1AllS.lean: the compiled verifier after the strict reader, on the files of this
library's own small test protocol. Files 1 to 21 of 21.

Sources. The files are those of Fmt/Toy1Files.lean: two honest ones and nineteen altered ones. The
protocol is a toy of this library's own, not the programs', and no file here comes from the
programs. The files were made outside Lean, with the format page's own reference program (a Python
script that belongs to the page, not the C++ prover), at an edition of the format page that is
not the one that ships (docs/format/FORMAT.md, which comes with the programs, the C++
implementation that comes with this Lean code; this file is not held against the page that
ships). That such files are still read is what the test below checks each time the file
compiles.

What is run. The file goes to the strict reader (`wholeChain`, Fmt/Rules8.lean), this library's
rendering of the format page's verifier up to its decision. The typed proof
string goes to `Compile.Batch.verifyOneProtocol` at the protocol's wiring with pruned openings, run with
BLAKE2b behind its oracles.

What is checked when the file compiles. One test (#guard): the outcome of every file, by name
(Run/ParseToy1.lean: reader, verifier, or accepted), and that a file is accepted exactly where the
reference program's own verifier has no reason to refuse (the table of Fmt/Toy1Files.lean).

Theorems. None. The count over all 21 files, and what these runs are not, are in
Run/ParseToy1All.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ParseToy1
import Fmt.Toy1Files

open Run Run.Toy1 in
#guard
  let r := ((_root_.Fmt.Toy1.files.drop 0).take 21).map fun x => (x.1, runStrict (1, 2, 3) x.2.1, x.2.2.isNone)
  (r.map fun y => (y.1, y.2.1)) == [("honest", Who.accepted), ("honest2", Who.accepted), ("alt01", Who.reader), ("alt02", Who.reader), ("alt03", Who.reader), ("alt04", Who.reader), ("alt05", Who.reader), ("alt06", Who.reader), ("alt07", Who.reader), ("alt08", Who.verifier), ("alt09", Who.reader), ("alt10", Who.reader), ("alt11", Who.reader), ("alt12", Who.reader), ("alt13", Who.reader), ("alt14", Who.reader), ("alt15", Who.reader), ("alt16", Who.verifier), ("alt17", Who.reader), ("alt18", Who.reader), ("alt19", Who.reader)] && r.all fun y => (y.2.1 == Who.accepted) == y.2.2
