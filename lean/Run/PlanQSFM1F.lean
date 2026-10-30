-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFM1F.lean: a test: the compiled verifier, with whole paths and challenges as sampled
values, at the first toy and the programs' own parameters, on files of this library's own: the full
parameters (the larger of the toy's two sets of sizes, full and tiny: `toyPar`, Fmt/M1Plan.lean); 13
files, the files 1 to 5 here. Challenges as sampled values: a round's verifier message is the values
that the format draws, not hash blocks (`ck`, Run/PlanDrawsQ.lean).

The first toy is a product test (on rows a, b, c with a_i b_i = c_i for every i; Fmt/M1Types.lean).
"The programs" are the C++ implementation that comes with this Lean code. The files here are this
library's own, not the programs': they were made outside Lean, by a reference program of this
library's own, at the programs' parameters (Fmt/M1FilesF.lean). The programs' own files are
judged in Run/PlanQSFProg.lean and the files that it gathers.

1. What is run. The run function `runFullS` (Run/PlanQSF.lean): the parser that fills whole paths,
   then the evaluable form of the compiled verifier at the wiring with whole paths, which is proved
   equal to the run of `Compile.Batch.verifyOneProtocol` there. The description is that of
   Fmt/M1PlanKnownF.lean; the decision is that of Fmt/M1All.lean.

2. What is checked when the file compiles (#guard). The outcome of every file, by name, compared
   with the part of the check that the reference program's table names (`fits`). This file has the
   definitions and the files 1 to 5; the others are in Run/PlanQSFM1Fb.lean and
   Run/PlanQSFM1Fc.lean.
   The honest file is accepted. A file at which the table names part 1 (form) has the outcome
   "reader". A file at which the table names one of the two checks of the last block (parts 4, 5)
   has the outcome "verifier". So has a file that was cut anew (`recut`), which only the proof of
   work can refuse.
   A file at which the table names work or openings (parts 2, 3) and that was not cut anew is
   refused. The verifier refuses it where the altered byte stands in an opening. It does so too
   where the positions that the altered hash chain draws ask for as many bytes as the file has. The
   reader refuses it where, after an altered nonce, root or random byte, the file no longer splits
   into the parts that these positions ask for. (At the tiny parameters such a copy passes a proof
   of work of six bits with chance 2^-6, and the reference program then names part 3.)

3. Theorems. None here.

4. What is not claimed. No statement on soundness follows. See the heads of Run/PlanQSF.lean and
   Run/PlanQSFProg.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSF
import Fmt.M1PlanKnownF
import Fmt.M1All

namespace Run.PQ.SFF
open _root_.Fmt.M1

/-- All files; beside each whether it is cut anew. -/
def all : List (String × ByteArray × Option FilesF.Dn × Bool) :=
  (FilesF.files.map fun x => (x.1, x.2.1, x.2.2, false)) ++
    FilesF.recut.map fun x => (x.1, x.2.1, x.2.2, true)

/-- Which outcomes fit the part of the check that the table names. -/
def fits : Option FilesF.Dn → Bool → Who → Bool
  | none, _, w => w == .accepted
  | some .d1, _, w => w == .reader
  | some .d2, true, w => w == .verifier
  | some .d2, false, w => w == .reader || w == .verifier
  | some .d3, _, w => w == .reader || w == .verifier
  | some _, _, w => w == .verifier

/-- The outcomes on the n files from place lo on; beside each whether it fits the table. -/
def spoke (lo n : Nat) : List (String × Who × Bool) :=
  ((all.drop lo).take n).map fun x =>
    let w := runFullS KnownF.spec (dec KnownF.par) x.2.1; (x.1, w, fits x.2.2.1 x.2.2.2 w)

end Run.PQ.SFF

open Run.PQ.SFF in
#guard all.length == 13
open Run.PQ Run.PQ.SFF _root_.Fmt.M1 in
#guard spoke 0 5 == [("honest", .accepted, true), ("bad-D1", .reader, true), ("bad-D1b", .reader, true), ("bad-D2", .reader, true), ("bad-D3", .verifier, true)]
