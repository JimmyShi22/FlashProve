-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseToy1All.lean: the small example of Run/ParseToy1.lean on 21 files made outside Lean: 2
accepted, 19 refused, by each of three run functions.

What is evaluated is `Compile.Batch.verifyOneProtocol`, the function that the compiler's verifier runs on
each proof string, its term untouched, with BLAKE2b behind its oracles. This file only gathers the
seven files with the tests, and states the count.

Sources. The files are in Fmt/Toy1Files.lean: two honest ones and nineteen altered ones, made with
the format page's own reference program (format_rules.py, a Python script that belongs to the page,
not the C++ prover) at an edition of the page that is not the one that ships.

1. What the file contains. Imports only.

2. What is checked when the seven files compile. The count, file by file, is in Run/ParseToy1AllLa,
Lb, Lc (first run function), Fa, Fb, Fc (second), S (third).
   First: the lenient reader, the wiring with pruned openings. Second: the parser that fills whole
   paths, the wiring with whole paths (the form of the wirings in the compiler's top theorems).
   These two give the same 21 answers. Both accept honest and honest2.
   In both, the verifier itself refuses eleven files:
        alt03 (a nonce that fails the test of work),
        alt04 (the next nonce that passes it: here the cut still fits),
        alt05 (a column),
        alt06 (a salt),
        alt07 (a given digest),
        alt08 (the last message),
        alt11 (two given digests swapped),
        alt16 (another honest row, the last message one too large),
        and the three copies that were cut anew for the positions that the altered chain draws:
        alt17 (a nonce that fails the test of work),
        alt18 (a bit of the root, nonce searched anew),
        alt19 (a bit of the random bytes, nonce anew).
   In both, eight files are refused by the reader, so that the verifier never sees them:
        alt01, alt02, alt14, alt15 (another random byte or root moves the drawn positions, and the
        file's length no longer fits the cut);
        alt09, alt10 (one byte short; one long);
        alt12, alt13 (a word that spells no element).
   The test of work is the test of a round's proof of work: its test bits must be zero.
   Third: the strict reader in front. Accepted: honest, honest2. The verifier refuses alt08, alt16
   (only the protocol's decision can). The reader refuses the other seventeen.
   By every run function a file is accepted exactly where the reference program's own verifier
   accepts it.

3. Theorems. None. Tests are evaluations; they leave no theorem.

4. What is not claimed.
   The protocol and the files are this library's own, not the programs'.
   In these seven files the oracles are typed oracle functions (those that a single oracle on the
   format's strings induces: Run/CodingFn.lean), not the one oracle through a coding with its
   proofs. The same example over a single oracle, through an encoding of the queries with its
   inverse and both laws, is in Run/ToyOne.lean.
   The verifier answers one bit: which of its tests refused is not shown. (Another verifier, on
   bytes, says which of its checks refuses: `Fmt.Toy1.why`, Fmt/Toy1.lean; a test there compares its
   answer, on each of the same 21 files, with the table `Fmt.Toy1.files`.) (For alt17 the reference
   program asserts that its own verifier accepts the file once the test of work is switched off.)
   The typed verifier accepts any first 256 bits of a leaf's salt: that they are the run's value is
   the parser's doing.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).
Limits: what the head of Run/ToyQ.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Run.ParseToy1AllLa
import Run.ParseToy1AllLb
import Run.ParseToy1AllLc
import Run.ParseToy1AllFa
import Run.ParseToy1AllFb
import Run.ParseToy1AllFc
import Run.ParseToy1AllS
