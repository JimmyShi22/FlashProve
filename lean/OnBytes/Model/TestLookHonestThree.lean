-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLookHonestThree.lean: a lookup of three calls, tested on an honest prover's
messages.

The prover, its data and what it does not show are described in OnBytes/Model/TestLookProver.lean.
With three calls of one tree each, no call has the number 3, and tree number 3 holds only padding.
The program does not import this file. Two more faults are in
OnBytes/Model/TestLookHonestThreeFaults.lean; the guards are in two files so that each compiles
quickly.

What is tested when the file compiles.
 1. On the honest prover's messages the walk goes through and all claims have the value 0.
 2. If one key is replaced by a value outside its call's table, the walk goes through and exactly
    one claim is not 0: the first claim of the tie, which compares the two products.
-/
import OnBytes.Model.TestLookProver

namespace OnBytes.Model.Forest.Honest

#guard allZero three {} == some true
-- 32 is no row of the last call's table
#guard notZeroAt three { key := some (2, 0, 32) } == some [0]

end OnBytes.Model.Forest.Honest
