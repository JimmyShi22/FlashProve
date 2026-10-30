-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullFd.lean: the verifier on bytes for the first toy, at the full parameters, on files of
this library's own: the decision refuses a cheating prover's file; by the reference program's table
the last block's check at a position refuses it first.

What is run. The run function `whoF` (Fmt/M1Full.lean), the verifier on bytes: the strict reader in
its fast form (proved equal to the reader of the rules at the format's hash), the view, the
decision; the head of Fmt/M1Full.lean says what the reader and the decision are. The sizes are the
full parameters: 30 rounds; three trees of depth 15, 14, 14, opened at 73, 74, 74 drawn positions;
20 bits of proof of work; files of 160,960 to 162,016 bytes. The parameter bytes are the programs'
own, byte for byte (Fmt/M1PlanKnownF.lean compares them with Fmt/M1Theirs.lean). The proof files
are this library's own, not the programs' (Fmt/M1FilesF.lean): they were made outside Lean by a
reference program of this library's own in Python, written independently of the Lean blocks. "The
programs" are the C++
implementation that comes with this Lean code.

What is checked when the file compiles. The file (`bad_D5`, Fmt/MustBeRefused/M1FilesF.lean) was
made by a cheating prover: one word of a sent row is made one larger before the row enters its
query, and all that follows is made by the honest rules. The reader reads the file. The test
(#guard) is on `spokeF` (Fmt/M1FullFw.lean), which gives a file's name, the outcome of `whoF` on it,
and the outcome that the reference program's table (Fmt/M1FilesF.lean) asks for. On this file both
outcomes are "decision".

Theorems. None. No Mathlib. The count over all thirteen files, and what these runs do not show, are
in Fmt/M1FullF.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1FullFw

open Fmt.M1 Fmt.M1.Full in
#guard spokeF ["bad-D5"] == [("bad-D5", .decision, .decision)]
