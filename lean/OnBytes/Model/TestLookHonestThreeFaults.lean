-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLookHonestThreeFaults.lean: a lookup of three calls, tested on two faulty provers.

The prover, its data and what it does not show are described in OnBytes/Model/TestLookProver.lean.
The honest prover's run and a first fault are in OnBytes/Model/TestLookHonestThree.lean. The
program does not import this file.

What is tested when the file compiles. In both cases the walk goes through, and the guard names the
claims that are not 0 (notZeroAt numbers them). The first claim of the tie, which compares the two
products, is among them both times.
 1. A bit of a count is replaced by 2: also the claim of the bits' sumcheck and the sum of the
    counts.
 2. A count is entered under the number 3, which no call has: also the planes' value at both points,
    since the planes' matrix has no column for that number. The sum of the counts does not see it.
-/
import OnBytes.Model.TestLookProver

namespace OnBytes.Model.Forest.Honest

-- bit 2 of the count of row 1 of call 1 is no bit
#guard notZeroAt three { bit := some ((1 * 4 + 1) * 32 + 2, 2) } == some [0, 50, 53]
-- a count of 1 for row 0 under the number 3, which is no call's
#guard notZeroAt three { bit := some (3 * 32, 1) } == some [0, 51, 52]

end OnBytes.Model.Forest.Honest
