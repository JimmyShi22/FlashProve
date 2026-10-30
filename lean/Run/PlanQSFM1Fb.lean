-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFM1Fb.lean: a test: the compiled verifier, with whole paths and challenges as sampled
values, at the first toy and the programs' own full parameters, on files of this library's own (made
outside Lean, by a reference program of this library's own, at the programs' parameters).
Files 6 to 10 of 13. Challenges as sampled values: a round's verifier message is the values that the
format draws, not hash blocks (`ck`, Run/PlanDrawsQ.lean).

What is run, whose the files are, and which outcome agrees with the table, is explained in
Run/PlanQSFM1F.lean.

What is checked when the file compiles. One test (#guard): the outcome of every file, by name.

Theorems. None here.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSFM1F

open Run.PQ Run.PQ.SFF _root_.Fmt.M1 in
#guard spoke 5 5 == [("bad-D4", .verifier, true), ("bad-D5", .verifier, true), ("bad-D1ca", .reader, true), ("bad-D1cb", .reader, true), ("bad-D1cc", .reader, true)]
