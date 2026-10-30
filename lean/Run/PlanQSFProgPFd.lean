-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFProgPFd.lean: a test: the compiled verifier, with whole paths, on the programs' own proof
files for the first toy, at the full parameters. Files 10 to 12 of 23.

"The programs" are the C++ implementation that comes with this Lean code. The two run functions, and
which outcome agrees with the tables that came with the files, are explained in
Run/PlanQSFProgPFw.lean.

What is checked when the file compiles. One test (#guard): the outcome of both run functions
("accepted", "reader" or "verifier") on every file, by name, and beside it that both agree with the
table that came with the files.

Theorems. None. The count over all files, and what these runs are not, are in Run/PlanQSFProg.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSFProgPFw

open Run.PQ Run.PQ.ProgPF in
#guard spokeV 9 3 == [("altered-10", .verifier, .verifier, true), ("altered-11", .reader, .reader, true), ("altered-12", .reader, .reader, true)]
