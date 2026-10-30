-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFProgPTb.lean: a test: the compiled verifier, with whole paths, on the programs' own proof
files for the first toy, at the tiny parameters. Files 12 to 22 of 31.

"The programs" are the C++ implementation that comes with this Lean code. The two run functions, and
which outcome agrees with the tables that came with the files, are explained in
Run/PlanQSFProgPTw.lean.

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
import Run.PlanQSFProgPTw

open Run.PQ Run.PQ.ProgPT in
#guard spokeV 11 11 == [("altered-12", .reader, .reader, true), ("altered-13", .reader, .reader, true), ("cheat-BASE_WRONG_WORD", .verifier, .verifier, true), ("cheat-CS_OTHER_MASK-0", .verifier, .verifier, true), ("cheat-CS_OTHER_MASK-1", .verifier, .verifier, true), ("cheat-CS_OTHER_MESSAGE-0", .verifier, .verifier, true), ("cheat-CS_OTHER_MESSAGE-1", .verifier, .verifier, true), ("cheat-CS_OTHER_TAIL-0", .verifier, .verifier, true), ("cheat-CS_OTHER_TAIL-1", .verifier, .verifier, true), ("cheat-FOLD_OTHER_ROWS", .verifier, .verifier, true), ("cheat-FOLD_WRONG_ROUND", .verifier, .verifier, true)]
