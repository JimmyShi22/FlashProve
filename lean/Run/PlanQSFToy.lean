-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFToy.lean: the compiled verifier with whole paths (each opened leaf has an authentication
path of its own), run on the 21 files of this library's own small test protocol and on the example
file of section 8 of the format page.

"The format page" is docs/format/FORMAT.md, which comes with the programs, the C++ implementation
that comes with this Lean code.

1. What is run. The run function `runFullS` (Run/PlanQSF.lean), from a description and a decision
   alone. The parser that fills whole paths is followed by `VPF`, which that file proves equal to
   the run of `Compile.Batch.verifyOneProtocol` at the description's protocol and the wiring with whole paths
   (`vpf_eq`).

2. What is checked when the file compiles (#guard).
   (1) This library's own small test protocol: the description and decision of Run/PlanQToy1.lean,
   and the 21 files of Fmt/Toy1Files.lean, which were made outside Lean. The outcome of every file,
   by name: 2 accepted; eleven refused by the verifier itself; eight by the reader. It is the same
   as for `Run.Toy1.runLax` and `Run.Toy1.runFull` in the tests that Run/ParseToy1All.lean gathers
   (the lists agree; no test compares them). These are two run functions of the form of that
   protocol that is written out term by term. A file is accepted exactly where the format page's
   reference program's own verifier has no reason to refuse.
   (2) The format page's example file of section 8 (a chain whose first round draws elements of the
   extension field; a tree of depth 3; proof of work), in both fields, with the decision "always
   yes": accepted. With one byte altered, at every eighth byte: never accepted. The outcome on each
   such copy is that of `runLaxS`, the run function with pruned openings behind the lenient reader.
   Pruned openings: the opened leaves of a tree share one set of sibling digests, as in the files.

3. Theorems. None here.

4. What is not claimed. What the heads of Run/ParseToy1All.lean and Run/PlanQSToy.lean list as not
   claimed.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSF
import Run.PlanQSToy
import Fmt.Toy1Files

open Run Run.PQ in
#guard
  let r := _root_.Fmt.Toy1.files.map fun x => (x.1, runFullS (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) x.2.1, x.2.2.isNone)
  (r.map fun y => (y.1, y.2.1)) == [("honest", Who.accepted), ("honest2", Who.accepted), ("alt01", Who.reader), ("alt02", Who.reader), ("alt03", Who.verifier), ("alt04", Who.verifier), ("alt05", Who.verifier), ("alt06", Who.verifier), ("alt07", Who.verifier), ("alt08", Who.verifier), ("alt09", Who.reader), ("alt10", Who.reader), ("alt11", Who.verifier), ("alt12", Who.reader), ("alt13", Who.reader), ("alt14", Who.reader), ("alt15", Who.reader), ("alt16", Who.verifier), ("alt17", Who.verifier), ("alt18", Who.verifier), ("alt19", Who.verifier)] && r.all fun y => (y.2.1 == Who.accepted) == y.2.2
open Run Run.PQ Run.PQ.TS in
#guard runFullS (K8 .two) yes _root_.Fmt.Known8.file2 == .accepted && runFullS (K8 .one) yes _root_.Fmt.Known8.file1 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard (places _root_.Fmt.Known8.file2).all fun i => runFullS (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) != .accepted && runFullS (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) == runLaxS (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i)
open Run Run.PQ Run.PQ.TS in
#guard (places _root_.Fmt.Known8.file1).all fun i => runFullS (K8 .one) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file1 i) != .accepted && runFullS (K8 .one) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file1 i) == runLaxS (K8 .one) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file1 i)
