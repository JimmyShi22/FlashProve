-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyTwoCodes.lean: tests of Chains.twoCodes (OnBytes/Model/VerifyStages.lean).

The condition two-codes of the standard parameter form requires that the table's folded row and the
message Omega have different codes, both in a batch's test on the table and in the key's one-time
test. Here the seven chains are made from the lines of the small example of
OnBytes/Params/TestFile.lean and the model's shapes of OnBytes/Params/TestConfigure.lean, which are
filled in by hand, so no layout file is needed. Then the folded row's two lines are set to Omega's:
in a batch's test, or in the key's one-time test. Each test is checked when the file compiles. The
file is no part of the program.

What this file does not show: that the C++ verifier finds the condition missed for the same
parameter files. No test here compares with it.
-/
import OnBytes.Model.VerifyStages
import OnBytes.Params.TestConfigure

namespace OnBytes.Model.TestVerifyTwoCodes

open Verify Params

/-- The lines l, with line `to` replaced by a copy of line `source` in which the text a is replaced
by b. Lines are counted from 0. -/
def withLineOf (l : List String) (to source : Nat) (a b : String) : List String :=
  l.set to ((l.getD source "").replace a b)

/-- The folded row's two lines set to Omega's, in a batch's test. -/
def batchOneCode (l : List String) : List String :=
  withLineOf (withLineOf l 16 18 "group omega" "group folded") 17 19 "stages omega" "stages folded"

/-- The same in the key's one-time test. -/
def onceOneCode (l : List String) : List String :=
  withLineOf (withLineOf l 22 24 "group once-omega" "group once-folded") 23 25 "stages once-omega"
    "stages once-folded"

/-- The seven chains under these lines, as chainsOf makes them from the bytes of the planner
(`configure`). The result is `none` if the lines are not read, the example's shapes are missing, the
planner refuses, or its bytes are not read back. -/
def chainsAt (l : List String) : Option Chains := do
  let x ← (readLines (TestFile.fileOf l)).toOption
  let shapes ← TestConfigure.shapes
  let made ← (configure x.1 shapes TestFile.smallCfg 0).toOption
  let key ← KeyChains.read made.keyOneTime made.keyShared made.keySecond
  let link ← Link.read made.entryLink
  let proof ← ProofChains.read made.first made.shared made.second
  pure { made := made, key := key, link := link, proof := proof }

-- lines 16 to 19 and 22 to 25 of the example are the lines that the functions above take them for
#guard [16, 17, 18, 19, 22, 23, 24, 25].map
    (fun i => ((TestFile.small.getD i "").splitOn " ").take 2) ==
  [["group", "folded"], ["stages", "folded"], ["group", "omega"], ["stages", "omega"],
   ["group", "once-folded"], ["stages", "once-folded"], ["group", "once-omega"],
   ["stages", "once-omega"]]
/-- Whether there are two codes in a batch's test, whether in the key's one-time test, and what the
condition says. -/
def says (l : List String) : Option (Bool × Bool × Bool) :=
  (chainsAt l).map fun c =>
    (c.proof.first.lin.sharedSplitNeeded, c.key.oneTime.lin.sharedSplitNeeded, c.twoCodes)

-- the example has two codes in both tests. Their lengths differ (fourth word of the group lines)
-- and so do their message lengths (fifth word). Two codes of one length are not tried
#guard says TestFile.small == some (true, true, true)
-- one code in a batch's test alone; in the key's one-time test alone
#guard says (batchOneCode TestFile.small) == some (false, true, false)
#guard says (onceOneCode TestFile.small) == some (true, false, false)

end OnBytes.Model.TestVerifyTwoCodes
