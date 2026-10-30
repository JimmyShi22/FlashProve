-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/HeadRounds.lean: the rounds of the output head's sub-proof, for the planner.

The plan of a proof's first chain lists every round with its error. The planner makes that list
from a few numbers of each sub-proof (OnBytes/Params/SubRounds.lean). This file gives the head's
numbers, from the head's layout and from the plan of its sub-proof (OnBytes/Model/HeadPlan.lean),
which is not the chain's plan. The C++ counterpart is the end of
verifier/src/vf_output_head_plan.inc, where the members own and rounds of the plan are set.

Main definitions: `HPlanH2.own`, `HPlanH2.rounds`.
What is not claimed: no theorem is stated here. None shows that the rounds listed here are those
that the check in OnBytes/Model/Head.lean runs. The dry run of that check (OnBytes/Iop/Ground.lean)
fails if the rounds' names, their order, their number or their numbers of draws differ from the
plan's. Degrees are not compared, and numbers of batched rows only in a run on a proof.
-/
import OnBytes.Model.HeadPlan
import OnBytes.Model.RoundSizes

namespace OnBytes.Model.Head

/-- The numbers of the sub-proof's own rounds. C++: the member own of the plan. -/
def HPlanH2.own (P : HPlanH2) (h : Shape) : Params.HeadRounds :=
  { lt := h.lt, lPd := h.lPd, lkW := P.lkW, sums := ledNS h.XL, products := ledNP h.XL,
    rowValues := ledNO h.XL, rows := P.rows }

/-- The rounds that follow the link's commitment number `moment`, which is 0, 1 or 2. After
commitment 0: the lookup and the sub-proof's own rounds. After 1: the matrix of the smallness test.
After 2: the rest of that test, the merge and the batching of all claims. A larger number is refused
(planSmall, OnBytes/Params/SubRounds.lean). C++: the member rounds of the plan. -/
def HPlanH2.rounds (P : HPlanH2) (h : Shape) (L : HL) (moment : Nat) : Params.Planning Unit :=
  Params.headRounds (forestSize L.fs) (P.own h) (smallSize P.tl) moment

end OnBytes.Model.Head
