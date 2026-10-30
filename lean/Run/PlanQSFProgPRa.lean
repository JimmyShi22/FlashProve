-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFProgPRa.lean: a test: the compiled verifier, with whole paths, on the programs' own proof
files for the first toy, at the tiny parameters with a repeated position. Files 1 to 14 of 14. A
repeated position: a position drawn twice is opened once: openings go by the drawn positions' set
(Fmt/Rules6.lean).

"The programs" are the C++ implementation that comes with this Lean code. The two run functions, and
which outcome agrees with the tables that came with the files, are explained in
Run/PlanQSFProgPRw.lean.

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
import Run.PlanQSFProgPRw

open Run.PQ Run.PQ.ProgPR in
#guard spokeV 0 14 == [("proof", .accepted, .accepted, true), ("altered-01", .reader, .reader, true), ("altered-02", .reader, .reader, true), ("altered-03", .reader, .reader, true), ("altered-04", .reader, .reader, true), ("altered-05", .reader, .reader, true), ("altered-06", .reader, .reader, true), ("altered-08", .verifier, .verifier, true), ("altered-09", .verifier, .verifier, true), ("altered-10", .verifier, .verifier, true), ("altered-11", .reader, .reader, true), ("altered-12", .reader, .reader, true), ("altered-13", .reader, .reader, true), ("altered-07", .verifier, .verifier, true)]
