-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/TestNormSizes.lean: the written lists of Point.lean, Squares.lean, Norm.lean and
Norm2.lean against the written lists of Cb/Pv/Head/Sizes.lean.

Sizes.lean lists, for the two example configurations, the head's numbers, the place and the sizes of
each sumcheck and every other round, as the verifier's planner makes them; tests beside that file
compute them anew from the examples' public files. Here the sizes at which the soundness properties
of the final norm's first blocks are stated, their numbers of scalars, their errors' numerators and
their slots are compared with these lists.

What is not claimed. A guard compares written lists. That a block's rounds send these numbers of
scalars is read off its definition, not tested here.


-/
import Cb.Pv.Head.Norm2
import Cb.Pv.Head.Sizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Test

/-- The rounds ZERO of the two examples. -/
def zeros : List OtherAt := others.filter fun o => o.name == "ZERO"

/-- The rounds that batch the nine sums. -/
def nines : List OtherAt := others.filter fun o => o.name == "BAT-sigma" && o.rows == 9

-- the sizes: 17 identities are the nine carries' lines and eight more
#guard pointSizes == headSizes.map fun h => ⟨h.lt, h.sums + 8⟩
#guard sqSizes == headSizes.map fun h => ⟨h.lt, h.lPd⟩
#guard norm2Sizes == (headSizes.zip nines).map fun z => (⟨z.1.lt, z.1.lPd⟩, z.2.slot)
-- ZERO: no scalar, lt draws
#guard zeros.length == 2 && (pointSizes.zip zeros).all fun z =>
  z.2.scalars == 0 && z.2.draws == z.1.lt
-- the batch: nine scalars, one draw, nine rows: the error's numerator is 8
#guard nines.length == 2 && nines.all fun o => o.scalars == 9 && o.draws == 1
-- the layer: no rider; lPd + lt rounds of two scalars; two in the further variable; two end
-- values; LINE
#guard (sqSizes.zip atSquares).all fun z =>
  z.2.riders == 0 && z.2.sent == List.replicate (z.1.lPd + z.1.lt) 2 && z.2.inY == 2 &&
    z.2.values == 2 && z.2.line
-- the errors' numerators: 1, the scalars of each round, those of the further variable, 0, 1
#guard (sqSizes.zip atSquares).all fun z => sqNums z.1 == 1 :: (z.2.sent ++ [z.2.inY] ++ [0]) ++ [1]
-- the rounds follow each other in the plan
#guard (zeros.zip (nines.zip atSquares)).all fun z =>
  z.2.1.place == z.1.place + 1 && z.2.2.place == z.1.place + 2
-- the slots: the hiding sum behind the nine; the end values behind 2 (lPd + lt) + 3 coefficients;
-- the first row product behind the two end values
#guard (norm2Sizes.zip atSquares).all fun z =>
  z.2.slot == z.1.2 + 9 && z.2.slotEnd == z.1.2 + 9 + (2 * (z.1.1.lPd + z.1.1.lt) + 3)
#guard (norm2Sizes.zip atTV).all fun z => z.2.slot == sPvOf z.1.2 z.1.1 + 7

end Cb.Pv.Head.Test
