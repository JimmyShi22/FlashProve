-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullProgPTa.lean: the verifier on bytes on the programs' own proof files for the first toy, at
the tiny parameters. Files 1 to 31 of 31.

"The programs" are the C++ implementation that comes with this Lean code. The verifier on bytes is
the run function `whoF` (Fmt/M1Full.lean). It applies the strict reader in its fast form
(`wholeChainF`, Fmt/Rules8Fast.lean), which is this library's rendering of the format page's
verifier up to its
decision (it cuts the file, recomputes the hash chain, tests the proof of work, and checks every
Merkle opening against its root), and then the decision (`dec`, Fmt/M1All.lean), the algebraic part
of the check. Its outcome names the first stage that refuses, "reader" or "decision", or is
"accepted". The format page is docs/format/FORMAT.md, which comes with the programs. The files, and
the outcome that each should have by the tables that came with the files, are in
Fmt/M1FullProgPTw.lean. A name
"cheat-X" is a false proof, made by the toy's own prover, in the programs, with one block cheating
in the named way.

What is checked when the file compiles. One test (#guard), on `spokeB lo n` (Fmt/M1FullProgPTw.lean;
n files from place lo on). It checks, for every file, the name, the outcome, and that the outcome
agrees (by stage alone: `fitsB`, Fmt/M1FullProgPTw.lean) with the table that came with the files;
for altered-07 the outcome agrees only in that the file is refused: its entry in `all`
(Fmt/M1FullProgPTw.lean) leaves the part of the check open. Fmt/M1FullProg.lean, part 2, says why.

Theorems. None. No Mathlib. The count over all files, and what these runs do not show, are in
Fmt/M1FullProg.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1FullProgPTw

open Fmt.M1 Fmt.M1.ProgPT in
#guard spokeB 0 31 == [("proof", .accepted, true), ("altered-01", .reader, true), ("altered-02", .reader, true), ("altered-03", .reader, true), ("altered-04", .reader, true), ("altered-05", .reader, true), ("altered-06", .reader, true), ("altered-08", .reader, true), ("altered-09", .reader, true), ("altered-10", .reader, true), ("altered-11", .reader, true), ("altered-12", .reader, true), ("altered-13", .reader, true), ("cheat-BASE_WRONG_WORD", .decision, true), ("cheat-CS_OTHER_MASK-0", .decision, true), ("cheat-CS_OTHER_MASK-1", .decision, true), ("cheat-CS_OTHER_MESSAGE-0", .decision, true), ("cheat-CS_OTHER_MESSAGE-1", .decision, true), ("cheat-CS_OTHER_TAIL-0", .decision, true), ("cheat-CS_OTHER_TAIL-1", .decision, true), ("cheat-FOLD_OTHER_ROWS", .decision, true), ("cheat-FOLD_WRONG_ROUND", .decision, true), ("cheat-PSC_END_VALUE", .decision, true), ("cheat-PSC_FALSE_TARGET", .decision, true), ("cheat-PSC_MU_FOR_GUESSED_EPS", .decision, true), ("cheat-PSC_OTHER_C", .decision, true), ("cheat-PSC_OTHER_W", .decision, true), ("cheat-PSC_ROUND", .decision, true), ("cheat-PSC_ROUND_Y", .decision, true), ("cheat-SEND_WRONG_ANSWER", .decision, true), ("altered-07", .reader, true)]
