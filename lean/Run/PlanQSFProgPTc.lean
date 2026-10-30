-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFProgPTc.lean: a test: the compiled verifier, with whole paths, on the programs' own proof
files for the first toy, at the tiny parameters. Files 23 to 31 of 31.

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
#guard spokeV 22 9 == [("cheat-PSC_END_VALUE", .verifier, .verifier, true), ("cheat-PSC_FALSE_TARGET", .verifier, .verifier, true), ("cheat-PSC_MU_FOR_GUESSED_EPS", .verifier, .verifier, true), ("cheat-PSC_OTHER_C", .verifier, .verifier, true), ("cheat-PSC_OTHER_W", .verifier, .verifier, true), ("cheat-PSC_ROUND", .verifier, .verifier, true), ("cheat-PSC_ROUND_Y", .verifier, .verifier, true), ("cheat-SEND_WRONG_ANSWER", .verifier, .verifier, true), ("altered-07", .reader, .reader, true)]
