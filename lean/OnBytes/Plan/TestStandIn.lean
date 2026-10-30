-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/TestStandIn.lean: the sizes and plans of a key at full size, under record.f2.txt of
blocks/frame/examples/. The tests run when this file compiles.

The C++ planning program (blocks/frame/cp_frame.cpp) prints what follows for a key whose proof of
the ranges looks up a stand-in shape: a matrix of 3,076,096 rows of bytes, of which 1,527,800 pairs
are the two digits of a weight. What is expected here was read from these prints: the group of the
multiplicities and the stages of the test on it; the columns of the table in the one-time test; the
number of rounds of the key's three chains together; and that no condition on the ranges is missed.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Plan.RangesGate
import OnBytes.Params.TestStandIn

namespace OnBytes.Plan.TestStandIn

open OnBytes.Params
open OnBytes.Params.TestExamples
open OnBytes.Params.TestStandIn (Printed printed)

/-- The stand-in shape of the planning program. -/
def standIn : Shape where
  kCol := 0
  matrixRows := 3076096
  lookups := [
    { lookup := { d := 8, mu := 0, live := 0, digitWeight := [1], offset := 128, paddingKey := 0,
                  parts := [], firstBound := [2, 1, 0, 5, 4, 3, 8, 7, 6] }
      entries := [⟨0, 0, 1527800, 1527800⟩, ⟨0, 3055600, 10248, 10248⟩]
      logRowsApart := 1 },
    { lookup := { d := 13, mu := 0, live := 0, digitWeight := [1, 256], offset := 4096,
                  paddingKey := 0, parts := [], firstBound := [2, 1, 0, 5, 4, 3, 8, 7, 6] }
      entries := [⟨0, 0, 1527800, 1527800⟩] }]

/-- What is compared for one parameter file: the test on the multiplicities as it is printed; the
row variables of its stages, main and mask (0 for the first stage's mask rows, which the prints do
not give); the columns of the one-time test; whether a key can be made; whether a condition on the
ranges is missed; the rounds of the three chains together, if all three plans are made and hold. -/
def keyOf (l : List String) :
    Option (Printed × List (Nat × Nat) × Nat × Bool × Bool × Option Nat) :=
  (readLines (TestFile.fileOf l)).toOption.bind fun x =>
    (keySized x.1 standIn).map fun z =>
      (printed z.set z.ranges.test.stages,
       (z.ranges.test.stages.take 1).map (fun s => (s.g.k, 0)) ++
         (z.ranges.test.stages.drop 1).map (fun s => (s.g.k, s.g.h)),
       z.once.shape.fold.columns, keyOk z, missedInTheRanges z,
       (do
         let a ← oneTimePlan z
         let b ← sharedPlan z.set z.codes z.once
         let c ← secondPlan z.set z.once
         pure (a.rounds.length + b.rounds.length + c.rounds.length)).toOption)

/-- The row variables of the four stages. -/
def rows : List (Nat × Nat) := [(4, 0), (4, 3), (3, 3), (0, 0)]

/-- The test under the rule "Johnson radius with slack". -/
def johnson : Printed :=
  (138, [(262144, 49, 4096, 49, 206, 49), (16384, 39, 2048, 39, 455, 39),
    (2048, 33, 1024, 33, 730, 33), (2048, 25, 4096, 25, 684, 25)])

#guard keyOf record == some (johnson, rows, 62, true, false, some 18950)

end OnBytes.Plan.TestStandIn
