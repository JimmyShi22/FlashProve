-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyHiding.lean: tests of the list of a request's range checks, and of the
condition on them (missedInTheChecks, OnBytes/Params/Gate.lean) at its threshold.

The matrices have the sizes of those in the five sub-proofs of a small configuration: the parameter
file and the scale file that are spelled out in OnBytes/Model/TestConfig.lean. Below, "the example"
means this configuration. The sizes come from a copy of the C++ verifier that was changed to print
its plans. That copy is not in the repository. One test compares the sizes with the plans that this
verifier makes. Each test is checked when the file compiles. The file is not part of the compiled
program.
-/
import OnBytes.Model.VerifySubproofs
import OnBytes.Model.TestConfig

namespace OnBytes.Model.TestVerifyHiding

open Params (RangeCheck rangeCheckBits missedInTheChecks)

/-- The closing part of a sub-proof with matrices of these rows and columns. -/
def tailOf (sizes : List (Nat × Nat)) (tau : Nat := 128) : HTailF2 :=
  { tau := tau, mats := (sizes.map fun s => { m := s.1, k := s.2 }).toArray }

/-- The matrices of a group of layers. The second group reads the last from the first group's
sub-proof. -/
def layers : List (Nat × Nat) :=
  [(8192, 247), (8192, 247), (8192, 247), (4096, 160), (4096, 14), (8192, 2048), (8192, 96),
   (8192, 20), (8192, 20)]

/-- The matrices of an attention sub-proof. The last is read from the sub-proof of its group of
layers. -/
def attention : List (Nat × Nat) := [(2048, 120), (4096, 4), (8192, 32), (8192, 1024), (8192, 96)]

/-- The matrices of the head. The last is read from the sub-proof of the last group of layers. -/
def head : List (Nat × Nat) := [(16384, 20), (4096, 16), (4096, 2), (8192, 1536), (8192, 20)]

/-- The example's range checks. -/
def checks : List RangeCheck :=
  rangeChecksH ([layers, attention, layers, attention, head].map (tailOf ·))

#guard rangeChecksH [] == []
#guard rangeChecksH [tailOf []] == []
#guard rangeChecksH [tailOf [(3, 5)] 160, tailOf [] 160, tailOf [(7, 11), (13, 17)] 160] ==
  [⟨3, 5, 160, 129, 131072, (10, 8)⟩, ⟨7, 11, 160, 129, 131072, (10, 8)⟩,
   ⟨13, 17, 160, 129, 131072, (10, 8)⟩]
-- each check has the number of combinations of its own closing part
#guard (rangeChecksH [tailOf [(3, 5)] 160, tailOf [(7, 11)] 128]).map (·.combinations) == [160, 128]
-- one check for each matrix, in the order of the links
#guard checks.length == 33
#guard checks.map (fun c => (c.rows, c.columns)) ==
  layers ++ attention ++ layers ++ attention ++ head
-- the digits represent the range exactly, so every check has a number of bits
#guard checks.all fun c => (rangeCheckBits c).isSome
-- the widest matrix has the fewest bits: 2^34 * 1.4426 / (2048 * 128^2) = 738, less 1 + 13 + 7
#guard (checks.filterMap rangeCheckBits).foldl min (2 ^ 30) == 717
#guard rangeCheckBits (rangeCheckOf 128 { m := 8192, k := 2048 }) == some 717

/-- The range checks that the verifier itself makes from the example's parameter file and scale
file: all plans of the sub-proofs are made, and the list is read off them. -/
def made : Option (List RangeCheck) :=
  (Verify.publicOf TestConfig.kit TestConfig.klFile none).toOption.bind Verify.rangeChecksOf

-- no sub-proof and no matrix is left out on the way from the files to the list
#guard made == some checks

/-- The three numbers of the example's parameter file that the condition reads: the line sec, the
line slots, and the fourth number of the line table, the random coordinates of a row. No other field
is read, and all others are left at their defaults. -/
def lines : Params.Lines :=
  { (default : Params.Lines) with sec := 128, slots := 64, tableRandom := 65535 }

/-- True if the condition is missed by the example's checks and one more, of a matrix with 8192 rows
and k columns. oneTime: the columns of the key's test on the table. first: the columns drawn of the
first table in a link. batches: the batches that a stored copy covers. -/
def missedWith (k oneTime first batches : Nat) : Bool :=
  missedInTheChecks lines (checks ++ [rangeCheckOf 128 { m := 8192, k := k }]) oneTime first batches

-- 1375, 44 and 1458 are oneTime, first and batches as the planner (Params.sized) derives them from
-- the example's two files and its layout file. The layout file is not spelled out in a test, so no
-- test here ties the three to the example. 717 bits less 6 + 6 + 11 + 11 are more than the line
-- sec's 128.
#guard !missedInTheChecks lines checks 1375 44 1458
-- a matrix with 12,000 columns would miss the condition: 126 bits before anything is taken off
#guard missedInTheChecks lines (rangeChecksH [tailOf [(8192, 12000)]]) 1375 44 1458
-- the threshold: 8265 columns give 183 bits, less 1 + 13 + 7 and 6 + 6 + 11 + 11: 128
#guard !missedWith 8265 1375 44 1458 && missedWith 8266 1375 44 1458
-- each of the three numbers alone decides at the threshold. batches: 2049 cost 12 bits, not 11.
-- The copies are 1 + (65535 - oneTime) / first: first = 31 gives 2070, above 2^11. At 8266 columns
-- oneTime = 20480 gives 1024 = 2^10 copies, a bit less, and the condition is met
#guard !missedWith 8265 1375 44 2048 && missedWith 8265 1375 44 2049
#guard !missedWith 8265 1375 32 1458 && missedWith 8265 1375 31 1458
#guard missedWith 8266 20479 44 1458 && !missedWith 8266 20480 44 1458

end OnBytes.Model.TestVerifyHiding
