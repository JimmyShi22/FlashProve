-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerTieOwed.lean: ONE STATEMENT THAT IS OWED FOR K14's LAW, AS A PROPOSITION
BY def: NO PROOF HERE. The seam at the shared chain's two proximity tests asks K1's tie (K1.Tie: the
premises under which a sample row reads as the library's) at the plan's three shapes: G_u's,
Omega's, the split's. K1's condition at a sending (condPort) gives the tie at every sampled message
of the sending (cond_tie, Johnson/Desc/K1/Law/Port6.lean). OWED: the three in the plan's own
letters.

  TiesOfCondOwed   from the condition at the two sendings and the shape's own conditions: the tie at
                   S.fold.u, S.omega and, where the row (Fold) is split, S.sharedSplit
What is not claimed. That it holds.
(It is proved in Johnson/Desc/K14/Law/LedgerTie.lean: tiesOfCond.)
That the condition holds at a plan. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.PlanShapesOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K1 (condPort Tie)

/-- OWED: K1's tie at the plan's three shapes. -/
def TiesOfCondOwed : Prop :=
  ∀ (Q : P14) (sentU : Array OracleNotice) (rad2 rad5 : ℕ → ℕ), withU Q.S = some sentU →
    Q.S.ok = true → condPort (parK1 Q 2 "o_u and the first mask" sentU) rad2 = true →
    condPort (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) rad5 = true →
    Tie Q.codes Q.S.fold.u ∧ Tie Q.codes Q.S.omega ∧
      (Q.S.sharedSplitNeeded = true → Tie Q.codes Q.S.sharedSplit)

end Desc.K14.Law
