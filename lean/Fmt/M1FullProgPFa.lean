-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullProgPFa.lean: the verifier on bytes on the programs' own proof files for the first toy, at
the full parameters. Files 1 to 6 of 23.

"The programs" are the C++ implementation that comes with this Lean code. The verifier on bytes is
the run function `whoF` (Fmt/M1Full.lean). It applies the strict reader in its fast form
(`wholeChainF`, Fmt/Rules8Fast.lean), which is this library's rendering of the format page's
verifier up to its
decision (it cuts the file, recomputes the hash chain, tests the proof of work, and checks every
Merkle opening against its root), and then the decision (`dec`, Fmt/M1All.lean), the algebraic part
of the check. Its outcome names the first stage that refuses, "reader" or "decision", or is
"accepted". The format page is docs/format/FORMAT.md, which comes with the programs. The files, and
the outcome that each should have by the tables that came with the files, are in
Fmt/M1FullProgPFw.lean.

What is checked when the file compiles. One test (#guard), on `spokeB lo n` (Fmt/M1FullProgPFw.lean;
n files from place lo on). It checks, for each of these files, the name, the outcome, and that the
outcome agrees with the table that came with the files.

Theorems. None. No Mathlib. The count over all files, and what these runs do not show, are in
Fmt/M1FullProg.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1FullProgPFw

open Fmt.M1 Fmt.M1.ProgPF in
#guard spokeB 0 6 == [("proof", .accepted, true), ("altered-01", .reader, true), ("altered-02", .reader, true), ("altered-03", .reader, true), ("altered-04", .reader, true), ("altered-05", .reader, true)]
