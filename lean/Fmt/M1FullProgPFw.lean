-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullProgPFw.lean: the programs' own proof files for the first toy, at the full parameters (30
rounds; trees of depth 15, 14, 14; 73, 74, 74 positions; 20 bits of work; files of some 160,000 to
162,000 bytes): the honest proof, 13 altered copies, 9 false proofs by cheating provers. The list of
files, and the outcome that each should have.

The first toy is a product test. The files were written by the programs (the C++ implementation that
comes with this Lean code): the honest proof by their CPU prover; the false proofs by a version of
it in which one block cheats; the altered copies are the honest proof with some bytes changed, its
last byte cut off, or a zero byte added (Fmt/M1ProgPFFiles.lean). All data in them are made up.

Sources. The bytes stand in Fmt/M1ProgPFFiles.lean, put there by a program from the files as they
came; those of the false proofs stand in the files that Fmt/MustBeRefused/M1ProgPF.lean gathers. The
outcome that each file should have is taken from the tables that came with the files.

1. What the file contains.
   `all`: every file, with its name, its bytes, and the part of the check at which it was expected
      to be refused (written down before the proof was made), for the false proofs, or at which the
      programs' C++ verifier refused it (altered copies). The part is a number (0: accepted; 1:
      form; 2: proof of work; 3: Merkle openings; 4 and 5: the two checks of the last block). "none"
      means refused, with the part left open. That is the one altered copy that fails both the
      linear check and the proof of work: which failure is met first depends on the order in which a
      verifier works.
   `fitsB`: which outcome of the verifier on bytes agrees with such a number. Its reader makes the
      tests of form, work and openings. So 0: accepted; 1, 2, 3: reader; 4, 5: decision; none, or
      any other number: not accepted.
   `spokeB lo n`: the outcome of the verifier on bytes on n files from place lo on, and whether it
      agrees.

The verifier on bytes is the run function `whoF` (Fmt/M1Full.lean). It applies the strict reader in
its fast form (`wholeChainF`, Fmt/Rules8Fast.lean), which is this library's rendering of the
format page's verifier up to its decision (it cuts the file, recomputes the hash chain, tests the
proof of work, and checks every Merkle opening against its root), and then the decision (`dec`,
Fmt/M1All.lean), the algebraic part of the check. Its outcome names the first stage that refuses,
"reader" or "decision", or is "accepted". The format page is docs/format/FORMAT.md, which comes with
the programs.

2. What is checked when the file compiles. Three tests (#guard), on the table and the parameter
bytes alone. The number of files, and that `noWord`, the list in Fmt/M1ProgPFFiles.lean of the files
without an entry in the tables that came with the files, is empty. The parameter bytes that came
with the files are those of the description in Fmt/M1PlanKnownF.lean (`KnownF.spec`). They are also
the bytes that Fmt/M1Theirs.lean holds (`Theirs.full`; made from the same archive).

3. Theorems. None. No Mathlib.

4. What is not claimed. This file runs no verifier. The outcomes are in Fmt/M1FullProgPFa.lean to
Fmt/M1FullProgPFd.lean; the count is in Fmt/M1FullProg.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1ProgPFFiles
import Fmt.M1FullFw
import Fmt.M1PlanKnownT
import Fmt.M1Theirs

namespace Fmt.M1.ProgPF

def all : List (String × ByteArray × Option Nat) :=
  (table.map fun x => (x.1, x.2.1, some x.2.2)) ++ refusedOnly.map fun x => (x.1, x.2, none)

def fitsB : Option Nat → Tiny.Who → Bool
  | some 0, w => w == .accepted
  | some 1, w => w == .reader
  | some 2, w => w == .reader
  | some 3, w => w == .reader
  | some 4, w => w == .decision
  | some 5, w => w == .decision
  | _, w => w != .accepted

/-- The outcome of the verifier on bytes, at `KnownF.spec` and `KnownF.par`, on n files from place
lo on, and beside each whether it agrees with the file's entry in `all`. -/
def spokeB (lo n : Nat) : List (String × Tiny.Who × Bool) :=
  ((all.drop lo).take n).map fun x =>
    let w := Full.whoF KnownF.spec KnownF.par x.2.1; (x.1, w, fitsB x.2.2 w)

end Fmt.M1.ProgPF

#guard Fmt.M1.ProgPF.all.length == 23 && Fmt.M1.ProgPF.noWord.isEmpty
#guard Fmt.M1.ProgPF.params == Fmt.M1.KnownF.spec.params
#guard Fmt.M1.ProgPF.params == Fmt.M1.Theirs.full
