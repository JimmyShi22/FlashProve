-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionHonestControlsScores.lean: a fourth control of the comparison in
OnBytes/Model/TestAttentionHonest.lean.

The test runs when this file is compiled. The program does not import this file.

As in OnBytes/Model/TestAttentionHonestControls.lean the record is altered, here in two places: the
last two challenges of the first sumcheck on the scores. The walk still goes through. The challenge
of the last round over the variables is a coordinate of the sumcheck's point, from which the weights
of that unit's two tables on qa are formed. So the tables change. The challenge of the round PSC Y
is the factor of the mask entries of the sumcheck's sixteen end values. So the factors change. Both
challenges enter claims, so the constant of the one equation and the coefficients on the slots
change too. None of the other six compared parts changes.
-/
import OnBytes.Model.TestAttentionHonestControls

namespace OnBytes.Attention.TestHonest

-- drawn element number 747 is the challenge of the round PSC Y, number 746 the one before it
#guard same (fun p => (p.alterDrawn 746).alterDrawn 747) ==
  some [false, true, false, false, true, true, false, true, true, true]

end OnBytes.Attention.TestHonest
