-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1FullProgPTw.lean: the programs' own proof files for the first toy, at the tiny parameters (22
rounds; 3, 3, 5 positions; 6 bits of work): the honest proof, 13 altered copies, 17 false proofs by
cheating provers. The list of files, and the outcome that each should have.

The first toy is a product test. The files were written by the programs (the C++ implementation that
comes with this Lean code): the honest proof by their CPU prover; the false proofs by a version of
it in which one block cheats; the altered copies are the honest proof with some bytes changed, its
last byte cut off, or a zero byte added (Fmt/M1ProgPTFiles.lean). All data in them are made up.

Sources. The bytes stand in Fmt/M1ProgPTFiles.lean, put there by a program from the files as they
came; those of the false proofs stand in Fmt/MustBeRefused/M1ProgPT.lean. The outcome that each file
should have is taken from the tables that came with the files.

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
bytes alone. The number of files, and that `noWord`, the list in Fmt/M1ProgPTFiles.lean of the files
without an entry in the tables that came with the files, is empty. The parameter bytes that came
with the files are those of the description in Fmt/M1PlanKnownT.lean (`KnownT.spec`). They are also
the bytes that Fmt/M1Theirs.lean holds (`Theirs.tiny`; made from the same archive).

3. Theorems. None. No Mathlib.

4. What is not claimed. This file runs no verifier. The outcomes are in Fmt/M1FullProgPTa.lean; the
count is in Fmt/M1FullProg.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1ProgPTFiles
import Fmt.M1FullFw
import Fmt.M1PlanKnownT
import Fmt.M1Theirs

namespace Fmt.M1.ProgPT

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

/-- The outcome of the verifier on bytes, at `KnownT.spec` and `KnownT.par`, on n files from place
lo on, and beside each whether it agrees with the file's entry in `all`. -/
def spokeB (lo n : Nat) : List (String × Tiny.Who × Bool) :=
  ((all.drop lo).take n).map fun x =>
    let w := Full.whoF KnownT.spec KnownT.par x.2.1; (x.1, w, fitsB x.2.2 w)

end Fmt.M1.ProgPT

#guard Fmt.M1.ProgPT.all.length == 31 && Fmt.M1.ProgPT.noWord.isEmpty
#guard Fmt.M1.ProgPT.params == Fmt.M1.KnownT.spec.params
#guard Fmt.M1.ProgPT.params == Fmt.M1.Theirs.tiny
