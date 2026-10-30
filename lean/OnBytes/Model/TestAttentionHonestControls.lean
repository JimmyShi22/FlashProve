-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionHonestControls.lean: controls of the comparison in
OnBytes/Model/TestAttentionHonest.lean.

The tests run when this file is compiled. The program does not import this file.

That comparison runs the check of the attention sub-proof on a record of an honest proof and finds
what the C++ verifier printed. Here the record is altered in one place. No round tests an equation,
so the walk still goes through. The test says which of the compared parts change.

Here a coefficient of a round of a sumcheck is altered. It changes the running claim of that
sumcheck. So the constant of the one equation (the sum of all claims under the powers of the
batching element; Fork.settle in OnBytes/Model/Hide.lean) changes, and none of the other nine
compared parts, which the function same lists.

Four of the ten parts follow from the plan and the sequence of the rounds, so no altered value can
change them: the number of claims, the numbers of virtual rows, whether the other arrays' weights
are 0, and the number of filled slots. Each of the other six changes in one of the controls.

A walk is slow to evaluate, so each control has a file of its own and the build can run them side by
side. The other three are OnBytes/Model/TestAttentionHonestControlsAlone.lean,
TestAttentionHonestControlsDrawn.lean and TestAttentionHonestControlsScores.lean.
-/
import OnBytes.Model.TestAttentionHonest

namespace OnBytes.Attention.TestHonest

open OnBytes.Model

/-- The walk on the altered record. Says for each compared part whether it is the recorded one: the
tables, the number of claims, the constant, the coefficients on the slots, the weights on the vector
of tables, what was shown under the slots, the factors of the mask entries, the numbers of virtual
rows, whether all weights on the other arrays are 0, and the number of filled slots. Returns none if
the walk fails. -/
def same (alter : Replay.Record → Replay.Record) : Option (List Bool) := do
  let P ← planOf 0
  let x ← stateOn P (alter (← Replay.ofText heard))
  let d := equationOf P.iU3 x.2
  let s := slotsOf 1929 x.2
  pure [tablesOf x.1 == seenTables, d.1 == nClaim, d.2.1 == c0, d.2.2.1 == onSlots,
    d.2.2.2.1 == onTables, s.1 == shownUnder, s.2.1 == factors, d.2.2.2.2.1 == rowsOf,
    d.2.2.2.2.2 == othersZero, s.2.2 == filled]

-- scalar number 1,500 is a coefficient of a round in the sub-proof's own part
#guard same (·.alterScalar 1500) ==
  some [true, true, false, true, true, true, true, true, true, true]

end OnBytes.Attention.TestHonest
