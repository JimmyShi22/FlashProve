-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionSums.lean: tests of OnBytes/Model/AttentionSums.lean.

The tests run when this file is compiled. The program does not import this file.

What is tested: the number of slots that a sumcheck of products takes, against the sum written out
by hand, and which slots its end values have. The sumchecks themselves are run in
OnBytes/Model/TestAttentionSumsHonest.lean.
-/
import OnBytes.Model.AttentionSums

namespace OnBytes.Attention.TestSums

-- 1 for the sum, 3 for each round, 2 for the further variable, 2 for each pair
#guard sc3Slots 0 1 == 1 + 0 + 2 + 2
#guard sc3Slots 3 2 == 1 + 9 + 2 + 4
#guard sc3Slots 17 40 == 1 + 51 + 2 + 80

-- the same count by the rule for rounds whose degrees differ
#guard sc3Slots 5 3 == Model.sumcheckSlotsDegrees (List.replicate 5 3) 6 2

-- the end values of pair 2 have the fifth and sixth slot, counted from that of the first end value
#guard (sc3A { sEnd := 10 } 2).slots == #[(14, oneE)]
#guard (sc3B { sEnd := 10 } 2).slots == #[(15, oneE)]
-- and these forms have nothing else: no entry of a virtual row, and the constant 0
#guard [sc3A { sEnd := 10 } 2, sc3B { sEnd := 10 } 2].all fun f => f.ents.isEmpty && isZeroE f.const

end OnBytes.Attention.TestSums
