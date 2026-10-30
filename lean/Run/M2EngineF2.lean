-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M2EngineF2.lean: runs files number 1 to 7 of 22 (counted from 0) of the programs' proof files
for the second toy (a chain of three links) through `run1PF`, `run1K`, `run1WPF`, `runFullSP`,
`runFullS`, `runLaxSP`, `runLaxS`, `runStrictSP`, `runStrictS`, `onBytes` (differing in reader,
typed or single oracle, challenges, pruned openings or whole paths: Run/M2EngineF1.lean, part 1;
`onBytes`: no compiled verifier). Link m: x_(m+1) = c_m = x_m b_m, entry by entry
(Fmt/M2Types.lean). Full parameters: 76 rounds; the honest proof has 249,456 bytes; 13 altered
copies; 8 false proofs. Tests only.

The programs are the C++ implementation that comes with this Lean code. The layout of their proof
files is fixed by the format page (docs/format/FORMAT.md, which comes with the programs; here in an
edition that is not the one that ships). A run function maps a file to an outcome; the outcome names
the first stage that refuses, or "accepted".

Sources. The bytes are the programs' own, made by the programs' own provers on a CPU (their "CPU
engine"), from the archive of files that the enclosed tools make (sha256
f97d6774317660e9033841ab36ce4e63e376ebeb25542cf6f1f92e8f61644aa1; the archive is not in this
repository): made-up toy data: no model, no weights. These test files were first made for an earlier
archive of the same toy, at an edition of the format page that is not the one that ships; between
the two archives the public file, the parameters' bytes, the statement, the plan and the codes are
the same byte for byte (compared by program), and the prover's coins differ. The bytes stand in
Fmt/M2ProgLFFiles.lean; the false proofs' in Fmt/MustBeRefused/M2ProgLF.lean and the files beside
it. The outcomes that the tests expect were first obtained by running all ten run functions on all
files of the archive. Which stage refuses was not foretold: there the tests record what the runs
gave. (Whether the lenient reader can still cut an altered copy can depend on the prover's coins.)

1. What the file contains. `S`, the description; `d`, the decision; `all`, the files; `part`, this
file's share of them. The rest of part 1 is that of Run/M2EngineF1.lean's head; it holds here too.

2. What is checked when the file compiles. 12 tests (#guard). (a) The description's parameters are
the archive's bytes; the number of files; the names of this file's share, in order. (b) The
conditions under which the theorems named under 3 of Run/M2EngineF1.lean's head hold
(Run/M2EngineDefs.lean: `tests`), at the description and at every file of this file's share. (c) For
each run function one string of letters, one letter per file (A accepted, V the verifier or, for
`onBytes`, the decision, R the reader): all 7 altered copies are refused.

3. Theorems. None here. Run/M2Tie.lean names the run functions' interfaces. The rest of part 3 is
that of Run/M2EngineF1.lean's head; it holds here too.

4. What is not claimed. No statement on soundness follows. `Compile.Batch.verifyOneProtocol` taken alone is
not the verifier of a scheme of which a theorem of the library speaks. That verifier runs three such
functions under a key. Here there is no such key. And the interfaces of these run functions have an
encoded index of length 0. With such an encoded index, what a theorem says about the language of an
accepted string is empty. No soundness statement is made in Run/ or Fmt/ for the protocol that these
files belong to. Part 4 of the head of Run/M2Tie.lean names some of what stands near it: statements
on building blocks, which nothing in Run/ or Fmt/ connects with this protocol, and conditions that
are true and empty. It is not claimed that the decision is the one that the programs compute: it is
a reading of the programs' description of the toy; the tests compare verdicts on the programs' own
files. Which check of the verifier, or of the reader, refuses is not shown. A letter of 2 (c) names
the stage; for `onBytes` (Run/M2EngineDefs.lean) the letter V says that the strict reader reads the
file and the decision refuses. A test (#guard) is an evaluation made while the file compiles; the
compile fails if the result moves; it leaves no theorem.

Terms: lean/GLOSSARY.md.
-/
import Run.M2EngineDefs
import Fmt.M2All
import Fmt.M2Theirs
import Fmt.M2ProgLFFiles

set_option autoImplicit false

namespace Run.PQ.M2EngineF2

abbrev S : _root_.Fmt.Spec := _root_.Fmt.M2.Theirs.specFull
abbrev d : PQ.View → Bool := _root_.Fmt.M2.dec _root_.Fmt.M2.toyPar

/-- the honest proof first; then the altered copies and the false proofs, in the order of the bytes'
file -/
def all : List (String × ByteArray) :=
  ("proof", _root_.Fmt.M2.ProgLF.proof) :: _root_.Fmt.M2.ProgLF.further

/-- this file's share -/
def part : List (String × ByteArray) := (all.drop 1).take 7

end Run.PQ.M2EngineF2

open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard S.params.data == _root_.Fmt.M2.ProgLF.params.data && all.length == 22 && part.map (·.1) == ["altered-01", "altered-02", "altered-03", "altered-04", "altered-05", "altered-06", "altered-07"]
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard tests S part
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part run1PF == "RRRRRRR"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part run1K == "RRRRRRR"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part run1WPF == "RRRRRRR"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part runFullSP == "RRRRRRR"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part runFullS == "RRRRRRR"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part runLaxSP == "RRRRRRR"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part runLaxS == "RRRRRRR"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part runStrictSP == "RRRRRRR"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part runStrictS == "RRRRRRR"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineF2 in
#guard voices S d part onBytes == "RRRRRRR"
