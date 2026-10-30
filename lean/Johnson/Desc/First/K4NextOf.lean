-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4NextOf.lean: A TERM, WITH CODE, OFF THE PUBLIC PARAMETERS ALONE, FOR THE LETTER
nextOf OF K4's LAYER OF THE TABLE OF JOINTS' FILLING (Johnson/Desc/First/FillK4.lean: "the public
parameters' next free slot in front of K4's sub-protocol", which the public item callerIn m compares
with the ledger's). One definition. No Mathlib.

  `nextOfPlan X m`: the lookup on the calls of segment m is MEANT to start at the public parameters'
    slot p.first (the lookups' public item lookIn asks, in front of that sub-protocol, that the
    ledger's next free slot be p.first) and to take as many slots as its shape has elements
    (`Forest.elems`): then in front of the caller's sub-protocol the ledger's next free slot is
    p.first + elems. Nothing where the link has no such lookup, or its parameters fix no shape.

Limits. A DEFINITION: NO LAW SAYS HERE that the ledger behind the lookup's yes stands at that number
(the lookups' law on what their sub-protocol leaves has it of their own hearing). It has not run as
it stands; by a run of our own runner, at one honest proof of each of two sizes, the ledger's next
free slot at the border in front of K4's sub-protocol was the one at the border in front of the
lookup plus the shape's elements, at every layers' place. General in the segment's sort: K4's layer
reads it at layers' segments alone. Nothing on soundness.
-/
import Johnson.Desc.First.Look.LookKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillK4
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (placeAt)

/-- The public parameters' next free slot behind segment m's lookup on the calls. -/
def nextOfPlan (X : Verify.Public) (m : Nat) : Option Nat :=
  (placeAt X m false).bind fun p => p.shape.map fun h => p.first + Forest.elems h

end VerifiableInference.Desc.First.FillK4
