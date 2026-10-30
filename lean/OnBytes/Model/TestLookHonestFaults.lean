-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLookHonestFaults.lean: a lookup of two calls, tested on three faulty provers.

The prover, its data and what it does not show are described in OnBytes/Model/TestLookProver.lean.
The honest prover's run and a first fault are in OnBytes/Model/TestLookHonest.lean. The program
does not import this file.

What is tested when the file compiles. In each case the walk goes through and exactly one claim is
not 0: the first claim of the tie, which compares the two products.
 1. One key is replaced by a different row of its own table, so that the counts are wrong.
 2. A padding place holds a row that is not the padding key.
 3. One key of call 0 is replaced by a row of call 1's table, and the counts are moved with it: one
    less for the row that the key pointed to, one more for that row of call 1. All counts add up and
    all bits are bits, so only the shift tells the key from the row.
-/
import OnBytes.Model.TestLookProver

namespace OnBytes.Model.Forest.Honest

-- a row of the call's own table, but not the row that was counted for this key
#guard notZeroAt two { key := some (1, 40, 1000 + 7 * ((two.rowOf 1 40 + 1) % 64).toUInt64) }
  == some [0]
-- a padding place that holds a row that is not the padding key
#guard notZeroAt two { key := some (0, 1010, 4) } == some [0]
-- 1063 is row 9 of call 1's table
#guard notZeroAt two { key := some (0, 17, 1063), moved := some ((0, two.rowOf 0 17), (1, 9)) }
  == some [0]

end OnBytes.Model.Forest.Honest
