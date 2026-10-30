-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/RowEq.lean: FROM SEVEN EQUATIONS TO A WRITTEN RECORD: the record that
`rowOf` (Table.lean) makes of the planner's sizes and its record of a group is a given record R, at
R's own three lists. One theorem; no number is evaluated.

What it is for: the law of the code switch asks of the typed record two tests with code, a third
beneath, and its level is a field; at the written records of LitRows.lean all four are theorems. So
an equation between `rowOf` at the plan in scope and a written record pays them.

Main names:
  `rowOf_eq`: z.set = R.set · z.codes = R.cs · n.before = R.g · radiusOf R.set R.g = R.rad · the
    planner's samples of the sending are R.o · the sending has R.roots trees · the last member's
    shape is R.rider: then rowOf z R.lo R.l R.kept n = R.
Limits. The seven equations are premises. That R.lo, R.l and R.kept are the planner's own lists is
not said. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.Table
import Johnson.Top.H0.K2Caller.LitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params OnBytes.Plan Johnson.Top.H

/-- **From seven equations to the written record**: the record that `rowOf` makes of the planner's
sizes z and its record n of a group, at the written record R's own lists, is R. -/
theorem rowOf_eq (z : ProofSized) (n : FrameN) (R : SwRow) (e1 : z.set = R.set)
    (e2 : z.codes = R.cs) (e3 : n.before = R.g) (e4 : radiusOf R.set R.g = R.rad)
    (e5 : reqSampled z.codes n.sent n.sendGroup z.batch.own.first n.riders = R.o)
    (e6 : treesOf z.codes n.sent.toArray = some R.roots)
    (e7 : ((n.members.getLast?).map (·.shape)).getD {} = R.rider) :
    rowOf z R.lo R.l R.kept n = R := by
  unfold rowOf oOf
  rw [e5, e6, e7, e3, e1, e2, e4]
  rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.rowOf_eq
