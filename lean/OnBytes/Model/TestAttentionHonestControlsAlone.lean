-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionHonestControlsAlone.lean: a further control of the comparison in
OnBytes/Model/TestAttentionHonest.lean.

The test runs when this file is compiled. The program does not import this file.

As in OnBytes/Model/TestAttentionHonestControls.lean the record is altered in one place. Here it is
a hidden value that is neither a scalar of a sumcheck nor the start of one. The walk still goes
through. The alteration changes what was shown under the value's slot, and none of the other nine
compared parts, which the function same of that file lists.
-/
import OnBytes.Model.TestAttentionHonestControls

namespace OnBytes.Attention.TestHonest

-- scalar number 1,427 is the first plane value of the first unit
#guard same (·.alterScalar 1427) ==
  some [true, true, true, true, true, false, true, true, true, true]

end OnBytes.Attention.TestHonest
