-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFM1R.lean: a test: the compiled verifier, with whole paths and challenges as sampled
values, at the first toy and the programs' own parameters, on files of this library's own: the tiny
parameters, with the random bytes of a first run of the programs; 46 files.

The first toy is a product test (on rows a, b, c with a_i b_i = c_i for every i; Fmt/M1Types.lean).
"The programs" are the C++ implementation that comes with this Lean code. The files here are this
library's own, not the programs': they were made outside Lean, by a reference program of this
library's own, at the programs' parameters (Fmt/M1FilesR.lean). The programs' own files are
judged in Run/PlanQSFProg.lean and the files that it gathers.

1. What is run. The run function `runFullS` (Run/PlanQSF.lean): the parser that fills whole paths,
   then the evaluable form of the compiled verifier at the wiring with whole paths, which is proved
   equal to the run of `Compile.Batch.verifyOneProtocol` there. The description is that of
   Fmt/M1PlanKnownR.lean; the decision is that of Fmt/M1All.lean.

2. What is checked when the file compiles (#guard). The outcome of every file, by name, compared
   with the part of the check that the reference program's table names (`fits`).
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
import Fmt.M1PlanKnownR
import Fmt.M1All

namespace Run.PQ.SFR
open _root_.Fmt.M1

/-- All files; beside each whether it is cut anew. -/
def all : List (String × ByteArray × Option FilesR.Dn × Bool) :=
  (FilesR.files.map fun x => (x.1, x.2.1, x.2.2, false)) ++
    FilesR.recut.map fun x => (x.1, x.2.1, x.2.2, true)

/-- Which outcomes fit the part of the check that the table names. -/
def fits : Option FilesR.Dn → Bool → Who → Bool
  | none, _, w => w == .accepted
  | some .d1, _, w => w == .reader
  | some .d2, true, w => w == .verifier
  | some .d2, false, w => w == .reader || w == .verifier
  | some .d3, _, w => w == .reader || w == .verifier
  | some _, _, w => w == .verifier

/-- The outcomes on the n files from place lo on; beside each whether it fits the table. -/
def spoke (lo n : Nat) : List (String × Who × Bool) :=
  ((all.drop lo).take n).map fun x =>
    let w := runFullS KnownR.spec (dec KnownR.par) x.2.1; (x.1, w, fits x.2.2.1 x.2.2.2 w)

end Run.PQ.SFR

open Run.PQ.SFR in
#guard all.length == 46
open Run.PQ Run.PQ.SFR _root_.Fmt.M1 in
#guard spoke 0 46 == [("honest", .accepted, true), ("alt-01", .reader, true), ("alt-02", .reader, true), ("alt-03", .reader, true), ("alt-04", .verifier, true), ("alt-05", .verifier, true), ("alt-06", .verifier, true), ("alt-07", .verifier, true), ("alt-08", .reader, true), ("alt-09", .reader, true), ("alt-10", .reader, true), ("cheat-01", .verifier, true), ("cheat-02", .verifier, true), ("cheat-03", .verifier, true), ("cheat-04", .verifier, true), ("cheat-05", .verifier, true), ("cheat-06", .verifier, true), ("cheat-07", .verifier, true), ("cheat-08", .verifier, true), ("cheat-09", .verifier, true), ("cheat-10", .verifier, true), ("cheat-11", .verifier, true), ("cheat-12", .verifier, true), ("cheat-13", .verifier, true), ("cheat-14", .verifier, true), ("cheat-15", .verifier, true), ("cheat-16", .verifier, true), ("cheat-17", .verifier, true), ("cheat-18", .verifier, true), ("cheat-19", .verifier, true), ("false-01", .verifier, true), ("word-0-03", .verifier, true), ("word-0-06", .verifier, true), ("word-1-00", .verifier, true), ("word-1-06", .verifier, true), ("word-1-12", .verifier, true), ("word-2-00", .verifier, true), ("word-2-03", .verifier, true), ("word-2-06", .verifier, true), ("word-2-09", .verifier, true), ("alt-11a", .reader, true), ("alt-11b", .reader, true), ("alt-11c", .reader, true), ("recut-16", .verifier, true), ("recut-20", .verifier, true), ("recut-22", .verifier, true)]
