-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestStandIn.lean: the derivation of a proof's sizes at a parameter file, with
stand-ins for the sub-proofs.

The C++ planning program (blocks/frame/cp_frame.cpp, `-plan request`) plans a proof of 25 equal
links, whose sub-proofs are stand-ins that meet known totals of rounds and scalars
(stand_in_subproofs in blocks/frame/files.h). This file has the same stand-ins. The numbers that are
expected were taken from that program's prints on record.f2.txt of blocks/frame/examples. Each test
is checked when the file compiles. The file is no part of the program.
-/
import OnBytes.Params.Gate
import OnBytes.Params.TestExamples

namespace OnBytes.Params.TestStandIn
open TestExamples

/-- An oracle message of a stand-in link. -/
def msg (rows deg masks moment life : Nat) : ReqMessage :=
  ⟨{ mainRows := rows, mainDeg := deg, maskRows := masks }, 0, moment, life⟩

/-- The rounds of a stand-in sub-proof after a moment. -/
def rounds (moment : Nat) : Planning Unit := do
  if moment == 0 then
    times 2 do
      planShift (2 ^ 21)
      planLkp 28
      planProductTree 28 0
      planProductTree 16 5
    times 4 do
      planZero 24
      planPsc { degree := List.replicate 24 4, degreeY := 3, values := 3 }
  else if moment == 1 then planRng (2 ^ 16)
  else
    planLkp 26
    planProductTree 26 0
    planBatt 14 22
    planScalars 560
    planBatSigma (2 ^ 14)

/-- Twenty-five equal links. -/
def standIn : Subproofs where
  links := (List.range 25).map fun l =>
    ⟨if l == 24 then 1 else 0,
     [msg 63 1 1 0 0, msg 7 1 0 0 0, msg 7 1 0 0 (if l < 24 then 1 else 0), msg 1 3 0 1 0,
      msg 27 1 0 2 0, msg 4 1 0 2 0]⟩
  openRows := List.replicate 25 (2 ^ 13)
  plan := fun _ => rounds
  pendingRows := 13
  matrixRows := 3076096

/-- A test as the planning program prints it: the integer of its first group's distance, and for
each stage the entries of a main message, its random entries, the same of a mask message, the list
size and the positions. -/
abbrev Printed : Type := Nat × List (Nat × Nat × Nat × Nat × Nat × Nat)

/-- What is printed of stages. -/
def printed (s : Setting) (st : List StageSize) : Printed :=
  ((st.head?.map (·.g.m)).getD 0,
   st.map fun x => (x.g.main.ell, x.g.main.r, x.g.mask.ell, x.g.mask.r, (analysis s x.g).list, x.t))

/-- What the planning program prints of a proof: the links' group, the last test, the three tests
on the table in a batch, the columns of a batch and the batches that a stored copy bears. Then:
whether all three plans are made and hold, and whether the gate's part on the links misses a
condition. -/
def proofOf (l : List String) :
    Option (Printed × Printed × Printed × Printed × Printed × Nat × Nat × Bool × Bool) :=
  (readLines (TestFile.fileOf l)).toOption.bind fun x =>
    (proofSized x.1 standIn).map fun z =>
      let plans := (proofPlans z standIn).toOption
      (printed z.set [⟨z.link.group, z.link.t, 0⟩], printed z.set z.last.stages,
       printed z.set z.batch.folded.stages, printed z.set z.batch.omega.stages,
       printed z.set z.batch.own.stages, z.batch.shape.fold.columns, z.batch.batches,
       plans.isSome,
       ((plans.bind (·.head?)).bind fun p =>
          (missedInTheLinks x.1 z standIn p).toOption).getD true)

#guard proofOf record == some
  ((258, [(4194304, 219, 8192, 219, 54, 219)]),
   (258, [(4194304, 219, 8192, 219, 54, 219),
     (262144, 55, 4096, 55, 238, 55),
     (32768, 55, 2048, 55, 362, 55),
     (4096, 55, 1024, 55, 546, 55),
     (256, 46, 256, 46, 798, 46),
     (256, 44, 1024, 44, 785, 44)]),
   (182, [(4194304, 101, 64, 152, 91, 101),
     (131072, 54, 256, 54, 222, 54),
     (8192, 54, 256, 54, 388, 54),
     (512, 54, 256, 54, 674, 54),
     (512, 51, 1024, 51, 711, 51)]),
   (159, [(262144, 3571, 64, 152, 237, 51),
     (16384, 51, 512, 51, 415, 51),
     (1024, 51, 256, 51, 711, 51),
     (1024, 41, 1024, 41, 681, 41)]),
   (159, [(262144, 3571, 256, 55, 237, 55),
     (16384, 55, 1024, 55, 415, 55),
     (2048, 55, 512, 55, 624, 55),
     (256, 46, 256, 46, 798, 46),
     (256, 44, 1024, 44, 785, 44)]),
   64, 688127, true, false)

end OnBytes.Params.TestStandIn
