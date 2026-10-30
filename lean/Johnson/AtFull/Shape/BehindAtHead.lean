-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BehindAtHead.lean: the smallness test's number among a link's hearing
sub-protocols: `k8No`; and that the driver's list of kinds has the kind K8 at that number:
`k8_index`. One definition, one theorem. Nothing is evaluated.

  `k8No sub`: 5 at the head's link, 4 at every other (DrawAtHead.lean's drawNo is the same
    function).
  `k8_index`: (kindsBeforeBatching sub first)[k8No sub]? = some KindName.K8, at every sort of link, whether or
    not the link is the first.

The sub-protocol "behind the batching" under the head, at all 25 links, is stated in SeatsNamed.lean
(behind_named, layers_named), with every step named and every parameter tied to a value.

The import lines say more than these two declarations need: files above reach modules through this
one; which of the five lines they need was not sought.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.BehindSeat
import Johnson.LPFK9R.SitsAtConstant
import Johnson.LPFK9R.SubsFull
import Johnson.IMR.K8Seat
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (Block Chain Link Place KindName Claim)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching K8.ParW)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.LinkJoin (SegAt batchAt)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T fullLinks)

/-- The smallness test's number among a link's hearing sub-protocols. -/
def k8No : ModelPart → Nat
  | .head => 5
  | _ => 4

theorem k8_index (sub : ModelPart) (first : Bool) :
    (kindsBeforeBatching sub first)[k8No sub]? = some KindName.K8 := by
  cases sub <;> cases first <;> rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.k8_index
#print axioms Johnson.AtFull.Shape.k8No
