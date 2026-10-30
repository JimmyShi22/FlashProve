-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/HeadLk.lean: at the full size the layout of the weights' matrix in the layers'
record has 2^18 columns. One closed fact proved by evaluation in Lean's kernel, at what the public
part's makers return (atMakers, Johnson/AtFull/Public/AtWitnesses.lean), with a negative test; and
its carrying to the makers' letters.

Why. The first slot of the lookup on the digits at the output head's link is the link's number of
slots, less the slots of the step on the weights that follows, less the lookup's own; the step's
number of slots hangs on this number alone (wsForkSlots, OnBytes/Model/Merge.lean).

  lk_W    [Lean's kernel] · lk_no: the test with 19 says no (it is false also where a maker refuses:
          lk_W is the control).
  lk_at   at the letters of the makers' equations: layers.wsLay.lk = 18.

Limits. The full size, at the stored free numbers alone. Nothing on soundness.
-/
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Public (atMakers at_witnesses OpensAt Makers)

theorem lk_W : atMakers (fun L _ _ => L.wsLay.lk == 18) = true := by decide +kernel

/-- A negative test. -/
theorem lk_no : atMakers (fun L _ _ => L.wsLay.lk == 19) = false := by decide +kernel

theorem lk_at {y : Layer.Lay} {sc : Layer.Scales} {wsLay : WsLay} {rope : Array Nat}
    {l : List Attention.Line} {ps : List Attention.Plan} {layers : Layer.Pub}
    {G : Array Layer.HPlan2} {seenA : Array SubPlan} (O : OpensAt y)
    (M : Makers y sc wsLay rope l ps layers G seenA) : layers.wsLay.lk = 18 :=
  beq_iff_eq.1 (at_witnesses O M (t := fun L _ _ => L.wsLay.lk == 18) lk_W)

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.lk_W
#print axioms Johnson.AtFull.K3X.lk_no
#print axioms Johnson.AtFull.K3X.lk_at
