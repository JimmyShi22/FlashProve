-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullF.lean: the verifier on bytes for the first toy, at the full parameters and the programs'
own parameter bytes, on thirteen files of this library's own: 1 accepted, 12 refused, each at the
stage that the table names.

The first toy is a product test. "The programs" are the C++ implementation that comes with this Lean
code; "the format page" is docs/format/FORMAT.md, which comes with the programs. This file only
gathers the files with the tests, which compile side by side, and states the count. No Mathlib. The
verifier on
bytes is `whoF` (Fmt/M1Full.lean); that file's head says what its two stages, the reader and the
decision, are.

1. The count.
   Fmt/M1FullFa.lean: the honest file (161,408 bytes): accepted.
   Fmt/M1FullFb.lean: seven files altered in form, work or an opening: reader.
   Fmt/M1FullFe.lean: three files that were cut anew (re-cut files), which only the proof of work
      can refuse (by the reference program's own assertion: Fmt/M1FullFe.lean): reader.
   Fmt/M1FullFc.lean, Fmt/M1FullFd.lean: two files by cheating provers, which the reader reads:
      decision.
   Fmt/M1FullFv.lean: the nineteen values from the honest file's bytes are the reference program's.

2. How a proof file of the programs is judged in the same way.
`Full.whoF KnownF.spec KnownF.par file` (or, from their parameter bytes alone, `specFrom` of
Fmt/M1Prog.lean), and `Full.valuesF` beside their nineteen printed values. The programs' own files
are judged so in Fmt/M1FullProg.lean and the files that it gathers.

3. Theorems. None. Tests are evaluations made while a file compiles; they leave no theorem.

4. What is not claimed. No statement on soundness follows.
   The files here are this library's own. This file's sources include no proof file of the
   programs. This file does not show that either implementation (the reference program's, Lean's)
   matches the programs', beyond the parameter bytes and four printed values (Fmt/M1Theirs.lean).
   Which of the decision's checks refuses is not shown. Which of the reader's tests (form, work,
   openings) refuses is not shown either: `wantsF` (Fmt/M1FullFw.lean) takes the table's parts 1, 2,
   3 alike for "reader" and 4, 5 alike for "decision", so an outcome is compared with the stage
   alone, not with the part that the table names. The outcome "decision" says only that the reader
   reads the file and `dec` (Fmt/M1All.lean) is false.
   The nineteen values are not taken from the decision's own run: `targets` walks the rounds by a
   copy of its steps, not by `decWith` itself (Fmt/M1Targets.lean, Limits).
   This is the verifier on bytes, by the format page's rules and by a reading of the programs'
   description of the toy. Nothing here connects it with the verifier of a theorem; that is the
   matter of the folder Run.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1FullFa
import Fmt.M1FullFb
import Fmt.M1FullFc
import Fmt.M1FullFd
import Fmt.M1FullFe
import Fmt.M1FullFv
