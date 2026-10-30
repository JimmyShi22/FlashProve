-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullFb.lean: the verifier on bytes for the first toy, at the full parameters, on files of
this library's own: the seven files altered in form, work or an opening are refused by the reader.

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

What is checked when the file compiles. The seven files, by their names in the test:
   bad-D1: the file is one byte short;
   bad-D1b: a word of the answer spells no field element;
   bad-D1ca, bad-D1cb, bad-D1cc: a word of the first opened column of a tree (one file for each
      tree) spells no field element;
   bad-D2: a byte of the last nonce is altered;
   bad-D3: a byte of a column of tree 2 is altered.
The test (#guard) is on `spokeF` (Fmt/M1FullFw.lean), which gives a file's name, the outcome of
`whoF` on it, and the outcome that the reference program's table (Fmt/M1FilesF.lean) asks for. On
each of the seven files both outcomes are "reader".

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
#guard spokeF ["bad-D1", "bad-D1b", "bad-D2", "bad-D3", "bad-D1ca", "bad-D1cb", "bad-D1cc"] == [("bad-D1", .reader, .reader), ("bad-D1b", .reader, .reader), ("bad-D2", .reader, .reader), ("bad-D3", .reader, .reader), ("bad-D1ca", .reader, .reader), ("bad-D1cb", .reader, .reader), ("bad-D1cc", .reader, .reader)]
