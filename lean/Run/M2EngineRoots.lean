-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M2EngineRoots.lean: tests that, at every file of the second toy (a chain of three links) whose
bytes are stored in this library and which the lenient reader reads, the Merkle roots that the file
sends are pairwise different.

The statements that give two verifiers the same verdict on a file ask a test on the file. The
statements are `core_lax` (Run/PageIsCore.lean), `core_one` and `core_tree`
(Run/PageIsCoreOne.lean [not in this library]). One verifier is the compiled verifier behind the lenient reader (the
reader first, then the verifier on what it hands out). The other is the format's strict verifier
(`Fmt.verify`, this library's rendering of it; that it renders the format page is not a theorem:
part 4 of the head of Run/PageIsCore.lean). The test is `rootsDiffer Fmt.formatHash S file`: "the roots that
the file sends are pairwise different as bytes". This file makes that test at all 69 files of the
second toy: the proof and the altered copies, at tiny parameters, at tiny parameters with a repeated
position, and at full parameters, and, at tiny and at full parameters, the false proofs.

Sources. The files' bytes are those of Fmt/M2ProgLTFiles.lean, Fmt/M2ProgLRFiles.lean,
Fmt/M2ProgLFFiles.lean and the files under Fmt/MustBeRefused/ that they import; where they come from
is said in the heads of these files. The reason for the test is rule R7.14 of the format page
(docs/format/FORMAT.md, which comes with the programs): the strict reader keeps one record of the
vertices met for every root that is opened, keyed by the root's 32 bytes, while the compiled
verifier walks each opened tree by itself; see the head of Run/PageIs.lean.

1. What the file contains.
   `readsAt S fs`: At how many files of a list the lenient reader (in its fast form, `laxWholeF`,
     Run/ParseLaxFast.lean) reads the file.
   `allDiffer S fs`: The test `rootsDifferF S file` (Run/RootsFast.lean) at every file of a list.
   `filesT`, `filesR`, `filesF`: The three lists: each bytes' file's "table" followed by its
     "refusedOnly".

2. What is checked when the file compiles. Tests (#guard), one pair for each of the three lists.
   The test on roots holds at every file of the list. Where the lenient reader does not read a file
     the test is true by definition. There the run functions behind the lenient reader refuse by
     construction, and the strict reader does not read the file either (the contrapositive of
     `pi_strict1`, Run/PageIsReaders.lean, which asks that the description lies within the limits,
     `ok S`, and that the hash has the format's digest lengths). So that "every file" is not hollow,
     the second test of each pair fixes the number of files in the list and the number at which the
     lenient reader reads: 33 and 23; 14 and 4; 22 and 12.

3. Theorems. None in this file. By `rootsF_eq` (Run/RootsFastProofs.lean)
`rootsDifferF S file = rootsDiffer Fmt.formatHash S file`; so each test gives the hypothesis of `core_lax`,
`core_one` and `core_tree` at that file.

4. What is not claimed.
   A test (#guard) is an evaluation made while the file compiles; it leaves no theorem.
   The other tests that `core_lax`, `core_one` and `core_tree` ask (`ok S`, `OKQ S`, `fourBounds`,
     `smallF S file`) are not made here.
   No statement on soundness follows.

Terms: lean/GLOSSARY.md.
-/
import Run.RootsFast
import Fmt.M2Theirs
import Fmt.M2ProgLTFiles
import Fmt.M2ProgLRFiles
import Fmt.M2ProgLFFiles

namespace Run.M2EngineRoots

/-- at how many files of a list the fast lenient reader reads -/
def readsAt (S : Fmt.Spec) (fs : List ByteArray) : Nat :=
  (fs.filter fun b => (Run.laxWholeF S b).isSome).length

/-- the test on roots at every file of a list -/
def allDiffer (S : Fmt.Spec) (fs : List ByteArray) : Bool := fs.all fun b => Run.PQ.rootsDifferF S b

def filesT : List ByteArray :=
  (Fmt.M2.ProgLT.table.map fun x => x.2.1) ++ Fmt.M2.ProgLT.refusedOnly.map fun x => x.2
def filesR : List ByteArray :=
  (Fmt.M2.ProgLR.table.map fun x => x.2.1) ++ Fmt.M2.ProgLR.refusedOnly.map fun x => x.2
def filesF : List ByteArray :=
  (Fmt.M2.ProgLF.table.map fun x => x.2.1) ++ Fmt.M2.ProgLF.refusedOnly.map fun x => x.2

end Run.M2EngineRoots

open Run.M2EngineRoots in
#guard allDiffer Fmt.M2.Theirs.specTiny filesT
open Run.M2EngineRoots in
#guard (filesT.length, readsAt Fmt.M2.Theirs.specTiny filesT) == (33, 23)
open Run.M2EngineRoots in
#guard allDiffer Fmt.M2.Theirs.specTiny filesR
open Run.M2EngineRoots in
#guard (filesR.length, readsAt Fmt.M2.Theirs.specTiny filesR) == (14, 4)
open Run.M2EngineRoots in
#guard allDiffer Fmt.M2.Theirs.specFull filesF
open Run.M2EngineRoots in
#guard (filesF.length, readsAt Fmt.M2.Theirs.specFull filesF) == (22, 12)
