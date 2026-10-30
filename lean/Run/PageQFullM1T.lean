-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQFullM1T.lean: tests: the first toy at the programs' tiny parameters (with random bytes of
this library's own), over the single oracle, at the wiring with whole paths, at both choices of
challenge types: one honest file accepted, all bad files refused, each with the outcome that the
files' table calls for, but for the files of the list `luck` (test (4)). (The first toy: a test
protocol of the programs, on rows a, b, c with a_i b_i = c_i.)

Tests only (#guard: evaluations made while the file compiles; they leave no theorem), and the
definitions that they need.
An outcome is a value of `Who` (Run/PlanQRun.lean): `accepted`, or who refuses: `limits`, `reader`,
`verifier`. `limits` is a refusal: the description fails `PQ.ok` (Run/PlanQTypes.lean) or, over a
single oracle, `OKQ` (Run/PageQ.lean).

What runs: Run/PageQFull.lean's `run1WF`. It is the parser that fills whole paths, then the
evaluable form of the compiled verifier. That form runs at the wiring `wqSF` (every opened leaf
climbs a whole path of its own) and at the typed oracle functions that the encoding of the queries
reads out of a single oracle on bit strings, BLAKE2b behind it. That encoding is made from the
description (Run/PageQ.lean: `pageQ`). By a theorem (`run1wf_eq`) `run1WF` is `run1W`. By a theorem
(`v1w_eq`) what `run1W` runs after the parser, `V1W`, is the run of `Compile.Batch.verifyOneProtocol` at
that wiring over that single oracle, all blocks asked. `run1WF` is run with challenges as sampled
values (`ck`), and with challenges as hash blocks (`ckP`; the library's "pull") (`run1WPF`). The
second is pulled and without the flag for pruned openings (`prJ`, Iop/BatchWire.lean): in these two
respects the form of the top theorems' own wirings.
The description: `Fmt.M1.KnownT.spec`; the decision: `Fmt.M1.dec` at its sizes; the files:
`Fmt.M1.FilesT` (with the re-cut ones); their table: `FilesT.files`, `FilesT.recut`: for each bad
file the part (`Dn`) at which the reference's verifier refuses it first.

Tests (#guard). (1) `ok S`, `OKQ S`, and `smallB S file` at every file.
(2) At each choice of challenge types: no file on which the run's outcome is not the one wanted
(Run/M1Run.lean: `wrong` .. (`wantLaxAt luck`) .. = []).
(3) "The verifier" is the wanted outcome on 38 of the 46 files, the honest file is one, the reader
on the other 7: with (2): the verifier itself refuses 38.
(4) Who is wanted: by the table's part and, at part 2, by whether the name begins with "recut"
(`wantLax`), but for the files of the list "luck" (listed by name), whose outcome depends on the
draws (Run/M1Run.lean: `wantLaxAt`); on each the lenient reader cuts the file exactly if "the
verifier" is the outcome that the list fixes. The files are this library's own reference's, made at
an edition of the format page that is not the one that ships.

Limits (what it is not): the files are this library's own: made outside Lean by a reference of this
library's own at the programs' parameters: not the programs' proof.
The parser calls the format's hash directly. That the run function's verdict is the definition's
run of a tree of queries is Run/Run1Full.lean's `run1WF_is`, `run1WF_pull`, statements
[not in this library; so here read: not proved in this library], under `ok S`, `OKQ S` and `smallF S
file` (Run/FullDom.lean). Of these
`smallF` is not a test here (`smallB` is). `verifyOneProtocol` taken alone belongs to no scheme under a
theorem: no soundness is claimed.
That this wiring is the compiler's generic wiring is not shown here. There is a theorem elsewhere
for challenges as hash blocks, but no equation with the library's forms for Batch is stated. The
theorem is on the compiler's generic wiring of a Test followed by the library's step for the work
tests (`Spec.planPull_wq` in Run/PlanPullWq.lean, proved in Run/PlanPullWqProofs.lean).
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.PageQFull
import Run.M1Run
import Run.LaxDom
import Fmt.M1PlanKnownT
import Fmt.M1FilesT

set_option autoImplicit false

namespace Run.PQ.M1WT
open Run.PQ _root_.Fmt.M1

def part : Option FilesT.Dn → Nat
  | none => 0
  | some .d1 => 1
  | some .d2 => 2
  | some .d3 => 3
  | some .d4 => 4
  | some .d5 => 5

/-- the files whose outcome after a lenient or whole-path reader depends on the draws: fixed by name
(Run/M1Run.lean: `wantLaxAt`) -/
def luck : List (String × Who) := [("alt-01", .verifier), ("alt-03", .verifier)]

/-- name, bytes, the table's part; the re-cut files after the others -/
def fs : List (String × ByteArray × Nat) :=
  (FilesT.files ++ FilesT.recut).map fun x => (x.1, x.2.1, part x.2.2)

/-- the run with challenges as sampled values (`ck`) -/
def runV (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  run1WF S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file

end Run.PQ.M1WT

open Run Run.PQ Run.PQ.M1WT _root_.Fmt.M1 in
#guard ok KnownT.spec && OKQ KnownT.spec && fs.all fun x => smallB KnownT.spec x.2.1
open Run Run.PQ Run.PQ.M1WT _root_.Fmt.M1 in
#guard Run.M1Run.wrong runV (Run.M1Run.wantLaxAt luck) KnownT.spec KnownT.par fs = []
open Run Run.PQ Run.PQ.M1WT _root_.Fmt.M1 in
#guard Run.M1Run.wrong run1WPF (Run.M1Run.wantLaxAt luck) KnownT.spec KnownT.par fs = []
open Run Run.PQ Run.PQ.M1WT _root_.Fmt.M1 in
#guard fs.length = 46 ∧ (fs.filter fun x => (Run.M1Run.wantLaxAt luck) x.1 x.2.2 = .verifier).length = 38 ∧ (fs.filter fun x => (Run.M1Run.wantLaxAt luck) x.1 x.2.2 = .accepted).length = 1 ∧ (fs.filter fun x => (Run.M1Run.wantLaxAt luck) x.1 x.2.2 = .reader).length = 7
-- the list of exceptions meets its conditions (`luckOK`: files of the set, of part 2 or 3, not
-- re-cut; never "accepted"); and on each of them the lenient reader cuts the file exactly if the
-- verifier is the outcome that the list fixes
open Run Run.PQ Run.PQ.M1WT _root_.Fmt.M1 in
#guard Run.M1Run.luckOK luck fs && luck.all fun e => fs.all fun x => x.1 != e.1 || Run.M1Run.laxReads KnownT.spec x.2.1 == (e.2 == .verifier)
