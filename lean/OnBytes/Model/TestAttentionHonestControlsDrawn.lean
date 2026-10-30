-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionHonestControlsDrawn.lean: a further control of the comparison in
OnBytes/Model/TestAttentionHonest.lean.

The test runs when this file is compiled. The program does not import this file.

As in OnBytes/Model/TestAttentionHonestControls.lean the record is altered in one place. Here it is
a coordinate of the drawn point at which the maxima are claimed. The walk still goes through. The
claims on the maxima read their table under weights that depend on that coordinate. So the weights
on the vector of tables change, and with them the constant of the one equation. None of the other
eight compared parts changes.
-/
import OnBytes.Model.TestAttentionHonestControls

namespace OnBytes.Attention.TestHonest

-- drawn element number 789 is the first coordinate of the point that is drawn for the maxima
#guard same (·.alterDrawn 789) ==
  some [true, true, false, true, false, true, true, true, true, true]

end OnBytes.Attention.TestHonest
