-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/BackRunLight.lean: in the layers' own rounds, the run "back" on
shapes (backG, Johnson/Desc/First/K4/Returns/RunShape.lean) is a function that builds no form. One
definition and two general laws, without a premise; nothing is evaluated.

Why. backG turns the shapes into forms with coefficients 0, runs the listing, and takes the forms'
shapes again. The listing subtracts each end form from a slot, and a difference of forms
(Aff.addMul, OnBytes/Model/Hide.lean) puts the subtrahend's entries one by one after the other's.
backRunLight appends two lists.

  backRunLight            the same test as backG's (the merge's sumcheck is open); the four claims'
                          shapes written outright: the batched sumcheck's row as the shape holds
                          it; one slot before each of the two end forms' shapes; the merge's
                          row off its sumcheck's shape; and backG's own ledger's shape after.
  backListing_shapes      the listing "back" (OnBytes/Desc/First/K4/Claims.lean) at the blank record
                          of a shape, seen through affSh, is that list of four.
  **backOnShapes_eqLight**   backG y sc ow L = backRunLight ow L, at every layout, table of scales,
                          shape and ledger's shape.

Limits. What either function costs Lean's kernel is not measured here. Nothing on the run "front".
That either returns at a shape which the chain reaches is not shown. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.RunShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open VerifiableInference.Desc.First.Shape

/-- **"back" on shapes, with no form built**: of the shape of what the hearing left and the ledger's
shape: the four claims' shapes and the ledger's shape after. -/
def backRunLight (ow : OwnSh) (L : LedSh) : Option (List AffSh × LedSh) :=
  if openB ow.wo.p L then
    some ([ow.K.rowS, (AffSh.mk [] [ow.K.sA0]).append ow.K.Alin,
        (AffSh.mk [] [ow.K.sB0]).append ow.K.Blin, rowOfSh ow.wo.p (AffSh.mk [] [])],
      (filledBy ow.wo.p L).setOwed (paidB (filledBy ow.wo.p L).owed ow.H.fo.owedJoin))
  else none

/-- The listing "back" at the blank record of the shape ow and the blank form of the shape r, seen
through affSh: ow's row of the batched sumcheck; one slot and then ow's end form, twice; r. -/
theorem backListing_shapes (y : Layer.Lay) (sc : Layer.Scales) (ow : OwnSh) (r : AffSh) :
    (back (ow.blank y sc []) r.blank).map affSh =
      [ow.K.rowS, (AffSh.mk [] [ow.K.sA0]).append ow.K.Alin,
        (AffSh.mk [] [ow.K.sB0]).append ow.K.Blin, r] := by
  show [affSh ow.K.rowS.blank, affSh (Aff.slot ow.K.sA0 - ow.K.Alin.blank),
    affSh (Aff.slot ow.K.sB0 - ow.K.Blin.blank), affSh r.blank] = _
  rw [affSh_sub, affSh_sub, affSh_slot, affSh_slot, affSh_blank, affSh_blank, affSh_blank,
    affSh_blank]

/-- **backG is backRunLight**: at every layout y, table of scales sc, shape ow and ledger's shape
L. -/
theorem backOnShapes_eqLight (y : Layer.Lay) (sc : Layer.Scales) (ow : OwnSh) (L : LedSh) :
    backG y sc ow L = backRunLight ow L := by
  unfold backG backRunLight
  rw [backListing_shapes]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.backRunLight
#print axioms OnBytes.Desc.First.K4.Rt.backListing_shapes
#print axioms OnBytes.Desc.First.K4.Rt.backOnShapes_eqLight
