-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/K9LensAsk.lean: ONE TEST WITH CODE ON PUBLIC NUMBERS, A SEGMENT AT A TIME:
"THE RUNS' CLAIMS ARE AT MOST THE PLAN's NUMBER": the closed numbers of claims of the segment's
runs, added up, are at most the plan's number of claims nLin.
Definitions alone. No Mathlib. HELD ASIDE: a candidate conjunct for the test `k9Entry`
(Johnson/Desc/First/Link/K9Asks.lean); it stands in no running text.

  `frontB y g`: the claims of the layers' run "front", its lookup's own rows not listed: off the
    layout's five numbers.
  `attOwnB S`: the claims of the attention's runs "first" and "second" together: the summands of the
    planner's own count (`Attention.ownClaims`) but the lookup's, the join's one and the planes'
    three.
  `ownLenB W l`: the segment's own runs' and its lookup on the calls' claims: layers: Forest.lins
    y.fo + frontB + 4 ("back"); attention: Forest.lins fs + attOwnB + 1 (the join) + 3 ("planes");
    the head: Forest.lins HLy.fs + 29 + 1 + 4 + 3 + 2 + 1.
  `lensFitB W l X`: **THE TEST**: ownLenB + (4 + (NM + the reads off the plan's tables)) +
Forest.lins X.tl.f9 ≤ the plan's nLin. EVERY "none" ENDS IN false: no plan of the group; no table
can be laid.
SECOND TEXTS: `frontB` repeats `frontLen false` (Johnson/Desc/First/K4/RunsLength.lean) at the
layout; `attOwnB` repeats six summands of `Attention.ownClaims` (OnBytes/Model/AttentionPlan.lean):
they will have to be turned with the texts that they repeat. `pairsAt`, `claimsAt` and `readsB` are
K9RowsAsk.lean's.
LOOPS AND POWERS: those of K9RowsAsk.lean, and `Attention.Counts.of S` (a fold over the shape's
calls, which the planner has run). The caller asks l < 25 alone.
Limits. A yes says what the clause says and no more. THAT THE RUNS' OWN NUMBERS ARE AT MOST THESE
CLOSED NUMBERS IS THE LAW's PREMISE, NOT THE TEST's WORD.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Link.K9RowsAsk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model

/-- The claims of the layers' run "front", the lookup's own rows not listed. -/
def frontB (y : Layer.Lay) (g : Nat) : Nat :=
  0 + 3 + 2 + 21 * y.NI + (y.NN * y.Lam + y.LamM + y.LamM * y.h.NE) + 6 + y.LamM + 3 +
    (if g == 0 then 1 else 0)

/-- The claims of the attention's runs "first" and "second" together. -/
def attOwnB (S : Attention.Shape) : Nat :=
  let x := Attention.Counts.of S
  let lt := S.cf.lt
  3 * x.nKRp + (6 * x.nKFp + 2 * x.sumNp) + (5 + lt + 2 * S.NP) + (1 + 4 * S.NP) +
    (4 * S.NP + S.Lam + S.NP * lt) + (x.nKFp + 5 + 1)

/-- The segment's own runs' and its lookup on the calls' claims. -/
def ownLenB (W : Verify.Public) (l : Nat) : Option Nat :=
  if l = 24 then some (Forest.lins W.HLy.fs + 29 + 1 + 4 + 3 + 2 + 1)
  else if l % 2 = 0 then some (Forest.lins W.layers.y.fo + frontB W.layers.y (l / 2) + 4)
  else (W.A[l / 2]?).map fun a => Forest.lins a.fs + attOwnB a.S + 1 + 3

/-- **THE TEST.** -/
def lensFitB (W : Verify.Public) (l : Nat) (X : Stages.LinkH) : Bool :=
  match ownLenB W l, pairsAt W l, claimsAt W l with
  | some a, some ps, some n =>
    decide (a + (4 + (X.tl.NM + readsB X.tl.NM X.tl.mats ps)) + Forest.lins X.tl.f9 ≤ n)
  | _, _, _ => false

end VerifiableInference.Desc.K9Asks
