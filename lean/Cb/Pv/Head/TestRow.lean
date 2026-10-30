-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/TestRow.lean: the written list of the errors of the row of the output head's own rounds
against the written lists of Cb/Pv/Head/Sizes.lean.

Sizes.lean lists, for the two example configurations, the place and the sizes of each sumcheck and
every other round of the head's sub-proof, as the verifier's planner makes them, and states the rule
of the plan's bounds. Here rowNums (Cb/Pv/Head/HeadRowNums.lean) is compared with that rule round by
round, behind its first member; the number of its members with the number of the plan's rounds from
the point over the positions up to the round before the smallness test; and the places of the row's
blocks with each other.

What is not claimed. A guard compares written lists. No test here calls a routine of the verifier.
The first member of rowNums counts points, lt q^(lt - 1) of q^lt: it is not compared here; the plan
has lt / q for that round.


-/
import Cb.Pv.Head.HeadRowNums
import Cb.Pv.Head.Sizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Test

/-- The numerators of a sumcheck's bounds, by the rule of Sizes.lean. -/
def boundsOf (x : PscAt) : List Nat :=
  1 :: (x.sent ++ [x.inY, 0]) ++ (if x.line then [1] else [])

/-- The two examples, each with the slot of the first of the nine sums. -/
def rowSizes : List (SqSize × Nat) := [(⟨6, 9⟩, 1531), (⟨10, 13⟩, 1995)]

/-- The five pieces of the plan's list for one example. -/
def planOf (i : Nat) : List Nat :=
  [8] ++ boundsOf (atSquares.getD i default) ++ [6] ++ boundsOf (atTV.getD i default) ++
    boundsOf (atTN.getD i default) ++ boundsOf (atTH.getD i default)

-- the errors behind the point's, round by round
#guard (List.range 2).all fun i =>
  (rowNums 7 (rowSizes.getD i (⟨0, 0⟩, 0)).1 (rowSizes.getD i (⟨0, 0⟩, 0)).2).drop 1 == planOf i
-- as many members as the plan has rounds from ZERO up to the round before the smallness test
#guard (List.range 2).all fun i =>
  (rowNums 7 (rowSizes.getD i (⟨0, 0⟩, 0)).1 (rowSizes.getD i (⟨0, 0⟩, 0)).2).length ==
    (atTH.getD i default).place + (boundsOf (atTH.getD i default)).length -
      (atSquares.getD i default).place + 2
-- the blocks follow each other in the plan
#guard (List.range 2).all fun i =>
  (atTV.getD i default).place ==
      (atSquares.getD i default).place + (boundsOf (atSquares.getD i default)).length + 1 &&
    (atTN.getD i default).place ==
      (atTV.getD i default).place + (boundsOf (atTV.getD i default)).length &&
    (atTH.getD i default).place ==
      (atTN.getD i default).place + (boundsOf (atTN.getD i default)).length

end Cb.Pv.Head.Test
