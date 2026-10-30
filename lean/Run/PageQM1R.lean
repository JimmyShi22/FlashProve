-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQM1R.lean: tests: the first toy at the programs' tiny parameters (with the programs' own
random bytes), over the single oracle, at both choices of challenge types: one honest file
accepted, all bad files refused, each with the outcome that the files' table calls for, but for the
files of the list `luck` (test (4)). (The first toy: a test protocol of the programs, on rows a, b,
c with a_i b_i = c_i.)

Tests only (#guard: evaluations made while the file compiles; they leave no theorem), and the
definitions that they need.
An outcome is a value of `Who` (Run/PlanQRun.lean): `accepted`, or who refuses: `limits`, `reader`,
`verifier`. `limits` is a refusal: the description fails `PQ.ok` (Run/PlanQTypes.lean) or, over a
single oracle, `OKQ` (Run/PageQ.lean).

What runs: `run1K` (Run/PageQKeep.lean) and `run1PF` (Run/PageQKeepC.lean). Each is the lenient
reader, then the evaluable form of the compiled verifier. That form runs at the typed oracle
functions that the encoding of the queries reads out of a single oracle on bit strings, BLAKE2b
behind it. That encoding is made from the description (Run/PageQ.lean: `pageQ`; with its inverse
and both laws). By theorems (`run1K_eq`, `run1pf_eq`) `run1K` is `run1` and `run1PF` is `run1P`. By
theorems (`v1_eq`, `v1c_eq`) what `run1` and `run1P` run after the reader, `V1` and `V1C`, is the
run of `Compile.Batch.verifyOneProtocol` over that single oracle, all blocks asked. `run1K` has challenges
as sampled values (`ck`); `run1PF` has challenges as hash blocks (`ckP`; the library's "pull")
(Run/PlanPull.lean), at which the conditions on a wiring (`OKG`) hold also where field elements are
drawn (`Spec.planPull_okg`, under its hypotheses).
The description: `Fmt.M1.KnownR.spec`; the decision: `Fmt.M1.dec` at its sizes; the files:
`Fmt.M1.FilesR` (with the re-cut ones); their table: `FilesR.files`, `FilesR.recut`: for each bad
file the part (`Dn`) at which the reference's verifier refuses it first.

Tests (#guard). (1) The three tests under which `Spec.run1_is` (Run/Run1Is.lean; proved in
Run/Run1IsProofs.lean) ties `run1`'s verdict to the definition's run of the tree (`tree1`): `ok S`,
`OKQ S`, and `smallB S file` at every file.
(2) At each choice of challenge types: no file on which the run's outcome is not the one wanted
(Run/M1Run.lean: `wrong` .. (`wantLaxAt luck`) .. = []): accepted for the honest file; the reader
for a fault of form or an altered byte in front of a draw that moves the cut; the verifier for a
fault in an opening, for a cheating prover, for a false statement, and for the re-cut files, which
were made so that only the verifier's own test of the work refuses them (by how this library's own
reference made them: no test here shows which check refuses).
(3) "The verifier" is the wanted outcome on 36 of the 46 files, the honest file is one, the reader
is wanted on the rest: with (2): the verifier itself refuses 36.
(4) Who is wanted: by the table's part and, at part 2, by whether the name begins with "recut"
(`wantLax`), but for the files of the list "luck" (listed by name): where a byte in front of a
draw, outside the openings, is altered, all later draws move. Whether the next test of work then
fails or passes by luck, and whether the openings in the file still have the lengths that the new
positions ask for, depends on the bytes. A test: on each such file the lenient reader cuts the file
exactly if "the verifier" is the outcome that the list fixes. Which of the verifier's checks
refuses there is not looked at. The files are this library's own reference's, made at an edition of
the format page that is not the one that ships.

Limits (what it is not): the files are this library's own: made outside Lean by a reference of this
library's own at the programs' parameters: not the programs' proof. The reader calls the format's
hash directly. `verifyOneProtocol` taken alone belongs to no scheme under a theorem: no soundness is
claimed.
That the two choices of challenge types give one verdict on every file is not proved in this file
(here it is seen on these files): it is stated in Run/PageIsOne.lean, `one_two`: `run1PF S dec file
= run1K S dec file` [not in this library; so here read: not proved in this library], under tests on
the
description and on the file that are stated there.

Terms: lean/GLOSSARY.md.
-/
import Run.PageQKeepC
import Run.M1Run
import Run.LaxDom
import Fmt.M1PlanKnownR
import Fmt.M1FilesR

set_option autoImplicit false

namespace Run.PQ.M1R
open Run.PQ _root_.Fmt.M1

def part : Option FilesR.Dn → Nat
  | none => 0
  | some .d1 => 1
  | some .d2 => 2
  | some .d3 => 3
  | some .d4 => 4
  | some .d5 => 5

/-- the files whose outcome after a lenient or whole-path reader depends on the draws: fixed by name
(Run/M1Run.lean: `wantLaxAt`) -/
def luck : List (String × Who) := [("alt-01", .reader)]

/-- name, bytes, the table's part; the re-cut files after the others -/
def fs : List (String × ByteArray × Nat) :=
  (FilesR.files ++ FilesR.recut).map fun x => (x.1, x.2.1, part x.2.2)

end Run.PQ.M1R

open Run Run.PQ Run.PQ.M1R _root_.Fmt.M1 in
#guard ok KnownR.spec && OKQ KnownR.spec && fs.all fun x => smallB KnownR.spec x.2.1
open Run Run.PQ Run.PQ.M1R _root_.Fmt.M1 in
#guard Run.M1Run.wrong run1K (Run.M1Run.wantLaxAt luck) KnownR.spec KnownR.par fs = []
open Run Run.PQ Run.PQ.M1R _root_.Fmt.M1 in
#guard Run.M1Run.wrong run1PF (Run.M1Run.wantLaxAt luck) KnownR.spec KnownR.par fs = []
open Run Run.PQ Run.PQ.M1R _root_.Fmt.M1 in
#guard fs.length = 46 ∧ (fs.filter fun x => (Run.M1Run.wantLaxAt luck) x.1 x.2.2 = .verifier).length = 36 ∧ (fs.filter fun x => (Run.M1Run.wantLaxAt luck) x.1 x.2.2 = .accepted).length = 1 ∧ (fs.filter fun x => (Run.M1Run.wantLaxAt luck) x.1 x.2.2 = .reader).length = 9
-- the list of exceptions meets its conditions (`luckOK`: files of the set, of part 2 or 3, not
-- re-cut; never "accepted"); and on each of them the lenient reader cuts the file exactly if the
-- verifier is the outcome that the list fixes
open Run Run.PQ Run.PQ.M1R _root_.Fmt.M1 in
#guard Run.M1Run.luckOK luck fs && luck.all fun e => fs.all fun x => x.1 != e.1 || Run.M1Run.laxReads KnownR.spec x.2.1 == (e.2 == .verifier)
