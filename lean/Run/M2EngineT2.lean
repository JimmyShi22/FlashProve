-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M2EngineT2.lean: runs files number 0 to 32 of 33 of the programs' proof files for the second toy
(a chain of three links) through `run1WPF`, `runFullSP`, `runFullS`. Link m: x_(m+1) = c_m = x_m
b_m, entry by entry (Fmt/M2Types.lean). Tiny parameters: 58 rounds; the honest proof has 12,800
bytes; 13 altered copies; 19 false proofs. Tests only.

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
Fmt/M2ProgLTFiles.lean; the false proofs' in Fmt/MustBeRefused/M2ProgLT.lean. The outcomes that the
tests expect were first obtained by running all ten run functions on all files of the archive. Which
stage refuses was not foretold: there the tests record what the runs gave. (Whether the lenient
reader can still cut an altered copy can depend on the prover's coins.)

1. What the file contains. `S`, the description; `d`, the decision; `all`, the files; `part`, this
file's share of them. The run functions of this file:
     `run1WPF` (Run/PageQFull.lean): lenient reader that fills in whole paths; the compiled verifier
       over a single oracle; challenges as hash blocks.
     `runFullSP` (Run/PlanQSFP.lean): lenient reader that fills in whole paths; typed oracle
       functions; challenges as hash blocks.
     `runFullS` (Run/PlanQSF.lean): lenient reader that fills in whole paths; typed oracle
       functions; challenges as sampled values.
   The words. A strict reader is this library's rendering of the format page's verifier up to its
     decision: it cuts the file, recomputes the hash chain from which the challenges are drawn,
     tests the proof of work and checks every Merkle opening against its root. A lenient reader only
     cuts the file into its parts and checks their form (it still recomputes the hash chain, because
     the drawn positions say how long the parts are). What the lenient reader refuses: part 1 of the
     head of Run/ParseLax.lean. The reader that fills in whole paths (`fullWhole`,
     Run/ParseFull.lean) does more: it also hashes the opened leaves and walks up each tree; it
     tests no proof of work and compares no root. The compiled verifier is the verifier of the
     non-interactive argument that the library's compiler makes of an interactive oracle protocol
     (`Compile.Batch.verifyOneProtocol`); what runs is an evaluable form of it; the theorems that tie the two
     are named under 3 of Run/M2EngineT1.lean's head. Here it asks three kinds of query (chain,
     leaf, node): either it is given typed oracle functions, one for each kind, made from the
     format's hash calls, or a single oracle on bit strings through an encoding of the queries.
     Challenges as sampled values or as hash blocks: whether a round's verifier message is the
     values that the format draws, field elements and positions among them, or the round's 256-bit
     blocks, from which reads and decision then draw. Pruned openings: the opened leaves of a tree
     share one set of sibling digests, as in the files; whole paths: each opened leaf has a path of
     its own.

2. What is checked when the file compiles. 5 tests (#guard). (a) The description's parameters are
the archive's bytes; the number of files; the names of this file's share, in order. (b) The
conditions under which the theorems named under 3 of Run/M2EngineT1.lean's head hold
(Run/M2EngineDefs.lean: `tests`), at the description and at every file of this file's share. (c) For
each run function one string of letters, one letter per file (A accepted, V the verifier or, for
`onBytes`, the decision, R the reader): the honest proof is accepted; all 13 altered copies are
refused; all 19 false proofs are refused.

3. Theorems. None here. Run/M2Tie.lean names the run functions' interfaces. The rest of part 3 is
that of Run/M2EngineT1.lean's head; it holds here too.

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
file and the decision refuses. (`onBytes` on these files: Run/M2EngineT4.lean.) A test (#guard) is
an evaluation made while the file compiles; the compile fails if the result moves; it leaves no
theorem.

Terms: lean/GLOSSARY.md.
-/
import Run.M2EngineDefs
import Fmt.M2All
import Fmt.M2Theirs
import Fmt.M2ProgLTFiles

set_option autoImplicit false

namespace Run.PQ.M2EngineT2

abbrev S : _root_.Fmt.Spec := _root_.Fmt.M2.Theirs.specTiny
abbrev d : PQ.View → Bool := _root_.Fmt.M2.dec _root_.Fmt.M2.tinyPar

/-- the honest proof first; then the altered copies and the false proofs, in the order of the bytes'
file -/
def all : List (String × ByteArray) :=
  ("proof", _root_.Fmt.M2.ProgLT.proof) :: _root_.Fmt.M2.ProgLT.further

/-- this file's share -/
def part : List (String × ByteArray) := (all.drop 0).take 33

end Run.PQ.M2EngineT2

open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineT2 in
#guard S.params.data == _root_.Fmt.M2.ProgLT.params.data && all.length == 33 && part.map (·.1) == ["proof", "altered-01", "altered-02", "altered-03", "altered-04", "altered-05", "altered-06", "altered-07", "altered-08", "altered-09", "altered-10", "altered-11", "altered-12", "altered-13", "cheat-BASE_WRONG_WORD", "cheat-CS_OTHER_KEPT-0", "cheat-CS_OTHER_KEPT-1", "cheat-CS_OTHER_KEPT_TAIL-0", "cheat-CS_OTHER_KEPT_TAIL-1", "cheat-CS_OTHER_MESSAGE-0", "cheat-CS_OTHER_MESSAGE-1", "cheat-CS_OTHER_MESSAGE-2", "cheat-CS_OTHER_PAD-0", "cheat-CS_OTHER_PAD-1", "cheat-FOLD_OTHER_ROWS", "cheat-FOLD_WRONG_ROUND", "cheat-PSC_END_VALUE", "cheat-PSC_FALSE_TARGET", "cheat-PSC_OTHER_C", "cheat-PSC_ROUND", "cheat-REQ_ROW_LEFT_OUT", "cheat-SEGMENTS_OTHER_CHAIN-0", "cheat-SEND_WRONG_ANSWER"]
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineT2 in
#guard tests S part
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineT2 in
#guard voices S d part run1WPF == "ARRRRRRRVVVRRRVVVVVVVVVVVVVVVVVVV"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineT2 in
#guard voices S d part runFullSP == "ARRRRRRRVVVRRRVVVVVVVVVVVVVVVVVVV"
open Run Run.PQ Run.PQ.M2E Run.PQ.M2EngineT2 in
#guard voices S d part runFullS == "ARRRRRRRVVVRRRVVVVVVVVVVVVVVVVVVV"
