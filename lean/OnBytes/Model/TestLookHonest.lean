-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLookHonest.lean: a lookup of two calls, tested on an honest prover's messages.

The prover, its data and what it does not show are described in OnBytes/Model/TestLookProver.lean.
The program does not import this file. Three more faults are in
OnBytes/Model/TestLookHonestFaults.lean; the guards are in two files so that each compiles quickly.

What is tested when the file compiles.
 1. On the honest prover's messages the walk goes through and all 55 claims have the value 0: the
    51 that read only mask entries, the three that read the planes, and the one on the key vectors.
 2. If one key is replaced by a row of the other call's table, the walk goes through and exactly one
    claim is not 0: the first claim of the tie, which compares the two products. The prover leaves
    the counts as they were, so this fault would break that comparison without a shift too;
    OnBytes/Model/TestLookHonestFaults.lean has the fault that only the shift tells.
-/
import OnBytes.Model.TestLookProver

namespace OnBytes.Model.Forest.Honest

#guard (valuesOn two {}).map (fun x => (x.size, x.all isZeroE)) == some (55, true)
-- 1063 is a row of the other call's table
#guard notZeroAt two { key := some (0, 17, 1063) } == some [0]

end OnBytes.Model.Forest.Honest
