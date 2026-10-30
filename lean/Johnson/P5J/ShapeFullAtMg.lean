-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/ShapeFullAtMg.lean: AT THE CONSTANT's OWN STRUCTURE (`AtMg`, AtMg.lean) THE FIRST
CHAIN's REQUEST's SHAPE, AS READ BACK, IS THE WRITTEN ONE: Zp.first.shape = shapeFull. One lemma
for all who take it as a premise ("hsh"). Two theorems: calls; at every letter o for the second
hash function.

By: AtMg.pins (Johnson/P5T/FenceAtMg.lean: the two entry tests on the written values accept) ·
pinnedAt_of_row · first_written_in_scope (Johnson/Goal/Numbers/MadeInScope.lean: its third
equation: the shape is the written sizes' request) · request_shape_written
(Johnson/Goal/Numbers/RequestWritten.lean: by the kernel: that request is shapeFull).

What is said. `AtMg.shape_full`: the equation. `AtMg.layout_full`: beside it, the layout of a
request's arrays is the written one (layout_in_scope, the same three premises).

Limits. AtMg is a premise: a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side
library AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.P5T.FenceAtMg
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Numbers.RequestWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (pinnedAt_of_row request_shape_written)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope layout_in_scope)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **THE FIRST CHAIN's SHAPE IS THE WRITTEN ONE.** -/
theorem AtMg.shape_full (h : AtMg o Z D r Zp Np cF) :
    Zp.first.shape = VerifiableInference.Desc.ReqLit.shapeFull := by
  have hZ : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  exact (first_written_in_scope h.scope hZ
    (pinnedAt_of_row (by rw [h.pins.1, Bool.or_true]))).2.2.1.trans request_shape_written

/-- And the layout of a request's arrays. -/
theorem AtMg.layout_full (h : AtMg o Z D r Zp Np cF) :
    Zp.first.layout = Johnson.G.layoutFull := by
  have hZ : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  exact layout_in_scope h.scope hZ (pinnedAt_of_row (by rw [h.pins.1, Bool.or_true]))

end P5J

#print axioms P5J.AtMg.shape_full
#print axioms P5J.AtMg.layout_full
