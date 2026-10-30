-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/TestVariants.lean: the sizes and plans of all three files at full size, under the
example parameter file and five variants of it. The tests run when this file compiles.

The file is blocks/frame/examples/record.f2.txt. Each variant changes a few of its lines: what
combining rows costs; the reading of the cited closeness theorem; the target; the requests in a
batch; work on every kind of round. The C++ planning program (blocks/frame/cp_frame.cpp,
`-plan request`) prints what follows from each, for stand-in shapes of the sub-proofs and of the
ranges. What is expected here was read from these prints by a program: for each of ten proximity
tests the integer of its first group's distance and, stage by stage, the entries and random entries
of a main and of a mask message, the list size and the positions; the number of rounds of the seven
chains together; the columns of the two tables in a link; the columns of a batch and the batches
that a stored copy bears.

The file's lines are also the first 32 lines of prover/examples/target_full_f2/policy.txt. The
length and the digest that are expected of the parameter bytes of an entry's chain were taken from a
run, on the proof of examples/full-size, whose three public files are that example's, of a copy of
the C++ verifier (not in this repository) that writes out what it hashes; the digest of the three
public files is the one that the C++ verifier's planning call prints for them (`configuration=`).

The ten tests, in the order of the lists: the links' group; the last test of the links; the folded
table, Omega and a request's own test in a batch; the same three in the committer's files; the
multiplicities of the ranges; the folded tables of a link between two tables.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Hash.H
import OnBytes.Plan.TestStandIn

namespace OnBytes.Plan.TestVariants

open OnBytes.Params
open OnBytes.Params.TestExamples
open OnBytes.Params.TestStandIn (Printed printed)

/-- What is compared for one parameter file: the ten tests; the rounds of the seven chains
together, 0 if a plan is refused or does not hold; the columns of the first and of the further table
in a link. -/
def allOf (l : List String) : Option (List Printed × Nat × Nat × Nat) := do
  let x ← (readLines (TestFile.fileOf l)).toOption
  let p ← proofSized x.1 Params.TestStandIn.standIn
  let k ← keySized x.1 TestStandIn.standIn
  let e ← (entrySized x.1).toOption
  let s := p.set
  let rounds : Except String Nat := do
    let a ← proofPlans p Params.TestStandIn.standIn
    let b ← oneTimePlan k
    let c ← sharedPlan s k.codes k.once
    let d ← secondPlan s k.once
    pure (a.foldl (fun n y => n + y.rounds.length) 0 + b.rounds.length + c.rounds.length +
      d.rounds.length + e.2.2.rounds.length)
  pure ([printed s [⟨p.link.group, p.link.t, 0⟩], printed s p.last.stages,
      printed s p.batch.folded.stages, printed s p.batch.omega.stages,
      printed s p.batch.own.stages, printed s k.once.folded.stages,
      printed s k.once.omega.stages, printed s k.once.own.stages,
      printed s k.ranges.test.stages, printed s e.1.linked.stages],
    rounds.toOption.getD 0, e.1.shape.columnsFirst, e.1.shape.columnsFurther)

/-- Lines with some lines put in others' places, by their numbers from 0. -/
def change (l : List String) (c : List (Nat × String)) : List String :=
  c.foldl (fun l x => l.set x.1 x.2) l

-- the file itself
#guard allOf record == some (
  [
    (258,
     [(4194304, 219, 8192, 219, 54, 219)]),
    (258,
     [(4194304, 219, 8192, 219, 54, 219), (262144, 55, 4096, 55, 238, 55),
      (32768, 55, 2048, 55, 362, 55), (4096, 55, 1024, 55, 546, 55),
      (256, 46, 256, 46, 798, 46), (256, 44, 1024, 44, 785, 44)]),
    (182,
     [(4194304, 101, 64, 152, 91, 101), (131072, 54, 256, 54, 222, 54),
      (8192, 54, 256, 54, 388, 54), (512, 54, 256, 54, 674, 54), (512, 51, 1024, 51, 711, 51)]),
    (159,
     [(262144, 3571, 64, 152, 237, 51), (16384, 51, 512, 51, 415, 51),
      (1024, 51, 256, 51, 711, 51), (1024, 41, 1024, 41, 681, 41)]),
    (159,
     [(262144, 3571, 256, 55, 237, 55), (16384, 55, 1024, 55, 415, 55),
      (2048, 55, 512, 55, 624, 55), (256, 46, 256, 46, 798, 46), (256, 44, 1024, 44, 785, 44)]),
    (182,
     [(4194304, 97, 64, 146, 91, 97), (131072, 52, 256, 52, 222, 52),
      (8192, 52, 256, 52, 388, 52), (512, 52, 256, 52, 676, 52), (512, 49, 1024, 49, 712, 49)]),
    (158,
     [(262144, 98, 64, 146, 238, 49), (16384, 49, 128, 49, 415, 49),
      (1024, 49, 64, 49, 712, 49), (1024, 39, 512, 39, 787, 39)]),
    (158,
     [(262144, 98, 256, 49, 238, 49), (16384, 49, 128, 49, 415, 49),
      (2048, 49, 64, 49, 625, 49), (256, 41, 64, 41, 1002, 41), (256, 29, 256, 29, 981, 29)]),
    (138,
     [(262144, 49, 4096, 49, 206, 49), (16384, 39, 2048, 39, 455, 39),
      (2048, 33, 1024, 33, 730, 33), (2048, 25, 4096, 25, 684, 25)]),
    (182,
     [(4194304, 97, 64, 97, 91, 97), (131072, 49, 128, 49, 274, 49),
      (8192, 49, 128, 49, 476, 49), (512, 50, 128, 50, 805, 50), (512, 40, 512, 40, 776, 40)])],
  71524, 62, 62)

/-- The columns of a batch and the batches that a stored copy bears. -/
def batchOf (l : List String) : Option (Nat × Nat) :=
  (readLines (TestFile.fileOf l)).toOption.bind fun x =>
    (proofSized x.1 Params.TestStandIn.standIn).map fun z =>
      (z.batch.shape.fold.columns, z.batch.batches)

#guard batchOf record == some (64, 688127)

/-- The digest of the three public files of prover/examples/target_full_f2. -/
def cfg : ByteArray :=
  Fmt.unhex "cf8ebe88802355fc0921fbbd3cc6aa770d01579b5750d1a88ab2d50cd0a5b118"

-- the parameter bytes of an entry's chain: their length and digest
#guard ((readLines (TestFile.fileOf record)).toOption.bind fun x =>
    (entryParams x.1 cfg).toOption.map fun b =>
      (b.size, Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm b))) ==
  some (5102, "deef21af0002223aebdaed4e79c489e4272e1085968cde5f399775490d3aa003")

/-- The file with the line "rowcost 2": combining rows costs a factor of their number. -/
def rowcost2 : List String :=
  change record [(3, "rowcost 2")]

#guard allOf rowcost2 == some (
  [
    (73,
     [(4194304, 225, 8192, 225, 15, 225)]),
    (73,
     [(4194304, 225, 8192, 225, 15, 225), (262144, 55, 4096, 55, 157, 55),
      (32768, 55, 2048, 55, 273, 55), (4096, 55, 1024, 55, 414, 55),
      (256, 46, 256, 46, 526, 46), (256, 44, 1024, 44, 785, 44)]),
    (79,
     [(4194304, 102, 64, 153, 40, 102), (131072, 54, 256, 54, 193, 54),
      (8192, 54, 256, 54, 337, 54), (512, 54, 256, 54, 587, 54), (512, 51, 1024, 51, 711, 51)]),
    (105,
     [(262144, 3571, 64, 153, 157, 51), (16384, 51, 512, 51, 273, 51),
      (1024, 51, 256, 51, 470, 51), (1024, 41, 1024, 41, 681, 41)]),
    (91,
     [(262144, 3571, 256, 55, 136, 55), (16384, 55, 1024, 55, 273, 55),
      (2048, 55, 512, 55, 472, 55), (256, 46, 256, 46, 604, 46), (256, 44, 1024, 44, 785, 44)]),
    (79,
     [(4194304, 98, 64, 147, 40, 98), (131072, 52, 256, 52, 194, 52),
      (8192, 52, 256, 52, 338, 52), (512, 52, 256, 52, 588, 52), (512, 49, 1024, 49, 712, 49)]),
    (104,
     [(262144, 98, 64, 147, 157, 49), (16384, 49, 128, 49, 273, 49),
      (1024, 49, 64, 49, 469, 49), (1024, 39, 512, 39, 787, 39)]),
    (91,
     [(262144, 98, 256, 49, 137, 49), (16384, 49, 128, 49, 273, 49),
      (2048, 49, 64, 49, 473, 49), (256, 41, 64, 41, 759, 41), (256, 29, 256, 29, 981, 29)]),
    (90,
     [(262144, 49, 4096, 49, 135, 49), (16384, 39, 2048, 39, 301, 39),
      (2048, 33, 1024, 33, 553, 33), (2048, 25, 4096, 25, 684, 25)]),
    (68,
     [(4194304, 99, 64, 99, 34, 99), (131072, 49, 128, 49, 157, 49),
      (8192, 49, 128, 49, 315, 49), (512, 50, 128, 50, 531, 50), (512, 40, 512, 40, 776, 40)])],
  71524, 66, 66)
#guard batchOf rowcost2 == some (69, 638262)

/-- The file with the line "reading 2": the other reading of the cited closeness theorem. -/
def reading2 : List String :=
  change record [(2, "reading 2")]

#guard allOf reading2 == some (
  [
    (258,
     [(4194304, 218, 8192, 218, 107, 218)]),
    (258,
     [(4194304, 218, 8192, 218, 107, 218), (262144, 55, 4096, 55, 475, 55),
      (32768, 55, 2048, 55, 723, 55), (4096, 55, 1024, 55, 1092, 55),
      (256, 46, 256, 46, 1595, 46), (256, 44, 1024, 44, 1568, 44)]),
    (182,
     [(4194304, 101, 64, 152, 182, 101), (131072, 54, 256, 54, 444, 54),
      (8192, 54, 256, 54, 774, 54), (512, 54, 256, 54, 1347, 54),
      (512, 51, 1024, 51, 1422, 51)]),
    (159,
     [(262144, 3571, 64, 152, 473, 51), (16384, 51, 512, 51, 830, 51),
      (1024, 51, 256, 51, 1422, 51), (1024, 41, 1024, 41, 1361, 41)]),
    (159,
     [(262144, 3571, 256, 55, 473, 55), (16384, 55, 1024, 55, 830, 55),
      (2048, 55, 512, 55, 1248, 55), (256, 46, 256, 46, 1595, 46),
      (256, 44, 1024, 44, 1568, 44)]),
    (182,
     [(4194304, 97, 64, 146, 182, 97), (131072, 52, 256, 52, 444, 52),
      (8192, 52, 256, 52, 775, 52), (512, 52, 256, 52, 1351, 52),
      (512, 49, 1024, 49, 1423, 49)]),
    (158,
     [(262144, 98, 64, 146, 475, 49), (16384, 49, 128, 49, 830, 49),
      (1024, 49, 64, 49, 1423, 49), (1024, 39, 512, 39, 1573, 39)]),
    (158,
     [(262144, 98, 256, 49, 475, 49), (16384, 49, 128, 49, 830, 49),
      (2048, 49, 64, 49, 1250, 49), (256, 41, 64, 41, 2004, 41), (256, 29, 256, 29, 1960, 29)]),
    (138,
     [(262144, 49, 4096, 49, 412, 49), (16384, 39, 2048, 39, 908, 39),
      (2048, 33, 1024, 33, 1459, 33), (2048, 25, 4096, 25, 1364, 25)]),
    (182,
     [(4194304, 97, 64, 97, 182, 97), (131072, 49, 128, 49, 547, 49),
      (8192, 49, 128, 49, 951, 49), (512, 50, 128, 50, 1609, 50),
      (512, 40, 512, 40, 1551, 40)])],
  71524, 60, 60)
#guard batchOf reading2 == some (63, 699049)

/-- The file with the target 100. -/
def sec100 : List String :=
  change record [(1, "sec 100")]

#guard allOf sec100 == some (
  [
    (12563,
     [(4194304, 161, 8192, 161, 2602, 161)]),
    (12563,
     [(4194304, 161, 8192, 161, 2602, 161), (262144, 41, 4096, 41, 11599, 41),
      (32768, 41, 2048, 41, 17575, 41), (4096, 41, 1024, 41, 26556, 41),
      (256, 34, 256, 34, 39370, 34), (256, 33, 1024, 33, 38236, 33)]),
    (8883,
     [(4194304, 73, 64, 110, 4442, 73), (131072, 37, 128, 37, 13324, 37),
      (8192, 37, 128, 37, 23163, 37), (512, 37, 128, 37, 39392, 37),
      (512, 30, 512, 30, 37947, 30)]),
    (7756,
     [(262144, 2661, 64, 110, 11557, 37), (16384, 37, 512, 37, 20181, 37),
      (1024, 37, 256, 37, 34721, 37), (1024, 30, 1024, 30, 33314, 30)]),
    (7756,
     [(262144, 2661, 256, 41, 11557, 41), (16384, 41, 512, 41, 20179, 41),
      (2048, 41, 256, 41, 30398, 41), (256, 34, 128, 34, 49045, 34),
      (256, 27, 512, 27, 46495, 27)]),
    (8883,
     [(4194304, 69, 64, 104, 4442, 69), (131072, 35, 128, 35, 13324, 35),
      (8192, 35, 128, 35, 23166, 35), (512, 35, 128, 35, 39446, 35),
      (512, 28, 512, 28, 37990, 28)]),
    (7734,
     [(262144, 70, 64, 104, 11600, 35), (16384, 35, 64, 35, 20182, 35),
      (1024, 35, 32, 35, 34746, 35), (1024, 28, 256, 28, 38291, 28)]),
    (7734,
     [(262144, 70, 256, 35, 11600, 35), (16384, 35, 128, 35, 20182, 35),
      (2048, 35, 64, 35, 30429, 35), (256, 29, 32, 29, 49316, 29),
      (256, 20, 256, 20, 48228, 20)]),
    (6749,
     [(262144, 35, 4096, 35, 10069, 35), (16384, 28, 2048, 28, 22157, 28),
      (2048, 23, 1024, 23, 35613, 23), (2048, 18, 4096, 18, 33283, 18)]),
    (8883,
     [(4194304, 69, 64, 69, 4442, 69), (131072, 35, 128, 35, 13324, 35),
      (8192, 35, 128, 35, 23166, 35), (512, 35, 128, 35, 39446, 35),
      (512, 28, 512, 28, 37990, 28)])],
  71524, 42, 42)
#guard batchOf sec100 == some (45, 978669)

/-- The file with 256 requests in a batch. -/
def slots256 : List String :=
  change record [(4, "slots 256")]

#guard allOf slots256 == some (
  [
    (258,
     [(4194304, 219, 8192, 219, 54, 219)]),
    (258,
     [(4194304, 219, 8192, 219, 54, 219), (262144, 55, 4096, 55, 238, 55),
      (32768, 55, 2048, 55, 362, 55), (4096, 55, 1024, 55, 546, 55),
      (256, 46, 256, 46, 798, 46), (256, 44, 1024, 44, 785, 44)]),
    (182,
     [(4194304, 101, 64, 153, 91, 101), (131072, 54, 256, 54, 222, 54),
      (8192, 54, 256, 54, 388, 54), (512, 54, 256, 54, 674, 54), (512, 51, 1024, 51, 711, 51)]),
    (161,
     [(262144, 14388, 64, 153, 234, 52), (16384, 68, 2048, 68, 267, 68),
      (1024, 69, 1024, 69, 459, 69), (1024, 68, 4096, 68, 470, 68)]),
    (161,
     [(262144, 14388, 256, 56, 234, 56), (16384, 55, 2048, 55, 359, 55),
      (2048, 56, 1024, 56, 538, 56), (256, 57, 512, 57, 697, 57),
      (256, 55, 2048, 55, 624, 55)]),
    (182,
     [(4194304, 97, 64, 146, 91, 97), (131072, 52, 256, 52, 222, 52),
      (8192, 52, 256, 52, 388, 52), (512, 52, 256, 52, 676, 52), (512, 49, 1024, 49, 712, 49)]),
    (158,
     [(262144, 98, 64, 146, 238, 49), (16384, 49, 128, 49, 415, 49),
      (1024, 49, 64, 49, 712, 49), (1024, 39, 512, 39, 787, 39)]),
    (158,
     [(262144, 98, 256, 49, 238, 49), (16384, 49, 128, 49, 415, 49),
      (2048, 49, 64, 49, 625, 49), (256, 41, 64, 41, 1002, 41), (256, 29, 256, 29, 981, 29)]),
    (138,
     [(262144, 49, 4096, 49, 206, 49), (16384, 39, 2048, 39, 455, 39),
      (2048, 33, 1024, 33, 730, 33), (2048, 25, 4096, 25, 684, 25)]),
    (182,
     [(4194304, 97, 64, 97, 91, 97), (131072, 49, 128, 49, 274, 49),
      (8192, 49, 128, 49, 476, 49), (512, 50, 128, 50, 805, 50), (512, 40, 512, 40, 776, 40)])],
  71524, 62, 62)
#guard batchOf slots256 == some (64, 688127)

/-- The file with work on every kind of round. -/
def workAll : List String :=
  change record [(7, "work field 10 11 12"),
    (8, "work sample 5 6 7"),
    (9, "work closeness 9 8 7"),
    (11, "work smallness 8 8 8")]

#guard allOf workAll == some (
  [
    (901,
     [(4194304, 217, 8192, 217, 187, 217)]),
    (901,
     [(4194304, 217, 8192, 217, 187, 217), (262144, 55, 4096, 55, 832, 55),
      (32768, 55, 2048, 55, 1261, 55), (4096, 55, 1024, 55, 1904, 55),
      (256, 46, 256, 46, 2788, 46), (256, 44, 1024, 44, 2735, 44)]),
    (554,
     [(4194304, 101, 64, 152, 277, 101), (131072, 54, 256, 54, 674, 54),
      (8192, 54, 256, 54, 1175, 54), (512, 54, 256, 54, 2046, 54),
      (512, 51, 1024, 51, 2158, 51)]),
    (484,
     [(262144, 3571, 64, 152, 720, 51), (16384, 51, 512, 51, 1260, 51),
      (1024, 51, 256, 51, 2158, 51), (1024, 41, 1024, 41, 2073, 41)]),
    (557,
     [(262144, 3571, 256, 55, 829, 55), (16384, 55, 1024, 55, 1448, 55),
      (2048, 55, 512, 55, 2177, 55), (256, 46, 256, 46, 2788, 46),
      (256, 44, 1024, 44, 2735, 44)]),
    (482,
     [(4194304, 97, 64, 146, 241, 97), (131072, 52, 256, 52, 588, 52),
      (8192, 52, 256, 52, 1026, 52), (512, 52, 256, 52, 1786, 52),
      (512, 49, 1024, 49, 1880, 49)]),
    (420,
     [(262144, 98, 64, 146, 631, 49), (16384, 49, 128, 49, 1097, 49),
      (1024, 49, 64, 49, 1880, 49), (1024, 39, 512, 39, 2076, 39)]),
    (420,
     [(262144, 98, 256, 49, 631, 49), (16384, 49, 128, 49, 1097, 49),
      (2048, 49, 64, 49, 1651, 49), (256, 41, 64, 41, 2647, 41), (256, 29, 256, 29, 2599, 29)]),
    (366,
     [(262144, 49, 4096, 49, 545, 49), (16384, 39, 2048, 39, 1203, 39),
      (2048, 33, 1024, 33, 1934, 33), (2048, 25, 4096, 25, 1806, 25)]),
    (482,
     [(4194304, 97, 64, 97, 241, 97), (131072, 49, 128, 49, 724, 49),
      (8192, 49, 128, 49, 1259, 49), (512, 50, 128, 50, 2124, 50),
      (512, 40, 512, 40, 2052, 40)])],
  71524, 60, 60)
#guard batchOf workAll == some (63, 699049)

end OnBytes.Plan.TestVariants
