-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullProg.lean: the verifier on bytes for the first toy, on the programs' own proof files. All
three honest proofs are accepted; all 39 altered copies and all 26 false proofs are refused; the
nineteen intermediate values are the programs'.

The first toy is a product test. "The programs" are the C++ implementation that comes with this Lean
code; "the format page" is docs/format/FORMAT.md, which comes with the programs. This file only
gathers the files with the tests, which compile side by side, and states the count.

Sources. The files were written by the programs: the honest proofs by their CPU prover; the false
proofs by a version of it in which one block cheats; the altered copies are the honest proof of
their set with some bytes changed, its last byte cut off, or a zero byte added. They are the files
that the enclosed tools make. They came in one archive, sha256
f97d6774317660e9033841ab36ce4e63e376ebeb25542cf6f1f92e8f61644aa1 (the archive is not in this
repository), which carries an edition of the format page that is not the one that ships. Their form
is the same at the edition that the archive carries and at a second edition of the format page, also
not the one that ships; both have two features: a leaf's label holds its column's width and its
salt's length; a stage is four words. The bytes stand in Fmt/M1ProgPFFiles.lean (full parameters),
Fmt/M1ProgPTFiles.lean (tiny parameters) and Fmt/M1ProgPRFiles.lean (tiny parameters with a repeated
position); those of the false proofs stand in Fmt/MustBeRefused/M1ProgPT.lean and in the files that
Fmt/MustBeRefused/M1ProgPF.lean gathers. Part 2 of the heads of the three files named first says how
the bytes are tied to the archive's checksums. All data in them are made up.

1. What is run. The run function `whoF` (Fmt/M1Full.lean): the strict reader in its fast form
(proved equal to the reader of the rules at the format's hash), the view, the decision. The reader
of the rules: `wholeChain`, Fmt/Rules8.lean; the proof: `wholeChainF_eq`, Fmt/Rules8Fast.lean. The
strict reader is this library's rendering of the format page's verifier up to its decision; the
decision is the algebraic part of the check. For the nineteen values: `valuesF` (Fmt/M1Full.lean),
with `targets` (Fmt/M1Targets.lean) in place of the decision. The descriptions are those of
Fmt/M1PlanKnownF.lean and Fmt/M1PlanKnownT.lean, whose parameter bytes are the programs' (a test
there).

2. What is checked when the gathered files compile (#guard). The outcome of every file, by name, is
compared with the tables that came with the files (by stage alone: part 4). For a false proof the
table says what was written down before any was made. For an altered copy it gives the words with
which the programs' C++ verifier refused it (the part is read off these words by a table in the
program that made the bytes' files).
   Full parameters (23 files): the proof (160,520 bytes) is accepted; 13 altered copies: reader; 9
      false proofs by cheating provers: decision.
   Tiny parameters (31 files): the proof (7,648 bytes) is accepted; 13 altered copies: reader; 17
      false proofs: decision.
   Tiny parameters with a repeated position (14 files): the proof (7,400 bytes) is accepted; 13
      altered copies: reader.
   One copy in each set (the seventh, altered-07, where the word shown in the last step is altered)
      fails the programs' linear check and also the proof of work of the last round. The programs'
      C++ verifier makes the linear check first (its words for this copy name that check). This
      library's verifier on bytes asks every query first and meets the proof of work, so its
      outcome is "reader"; the tests have this outcome; of this copy `fitsB` (part 4) asks only that
      it is not accepted; which of the reader's tests refuses it is not tested.
   The nineteen values computed from each proof's bytes are those that the programs' tool prints, in
      all three sets. The head of Fmt/M1Targets.lean lists them in order and says what a block and a
      target are. The nineteen values are:
        the targets after the blocks;
        the folded symbols at each switch's first draw;
        the first entry of each switch's c, and the first and the last entry of its d;
        both sides of the last linear check.

3. Theorems. None. No Mathlib. Tests are evaluations made while a file compiles; they leave no
theorem.

4. What is not claimed. No statement on soundness follows. Which of the decision's two checks
refuses a false proof is not shown. Which of the reader's tests (form, work, openings) refuses an
altered copy is not shown either: `fitsB` (Fmt/M1FullProgPFw.lean, Fmt/M1FullProgPTw.lean,
Fmt/M1FullProgPRw.lean) takes the tables' parts 1, 2, 3 alike for "reader" and 4, 5 alike for
"decision", so an outcome is compared with the stage alone, not with the part that a table names.
The outcome "decision" says only that the reader reads the file and `dec` (Fmt/M1All.lean) is false.
The nineteen values are not taken from the decision's own run: `targets` walks the rounds by a copy
of its steps, not by `decWith` itself (Fmt/M1Targets.lean, Limits). This is the verifier on bytes,
by the format page's rules and by a reading of the programs' description of the toy. Nothing here
connects it with the verifier of a theorem; that is the matter of the folder Run.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1FullProgPTa
import Fmt.M1FullProgPTv
import Fmt.M1FullProgPRa
import Fmt.M1FullProgPRv
import Fmt.M1FullProgPFa
import Fmt.M1FullProgPFb
import Fmt.M1FullProgPFc
import Fmt.M1FullProgPFd
import Fmt.M1FullProgPFv
