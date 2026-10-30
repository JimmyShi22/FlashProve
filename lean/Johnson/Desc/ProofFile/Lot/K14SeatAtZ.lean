-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean: the whole shared chain of a proof file's description at
the maker's public part Z (Johnson/Desc/ProofFile/Pub.lean).

This file holds definitions only; no theorem is stated.

beforePointOf N: the first chain's message that must be fixed before the shared point is drawn, off
the plan: of what the last chain's own proximity test says must be sent before its first draw, the
first chain's message with the greatest number.

sharedSeatAt Z: sharedSeatOf (Johnson/Desc/ProofFile/Lot/K14Seat.lean) at the planner's chains. The
two proximity tests and the chain's end are those of Johnson/Desc/K12/Seat/Fill.lean, at the places'
numbers made of the plan. No stand-in is named. For fileOk it hands on the file's own share of the
tests on the plan (Johnson/Desc/OnPlan/OkBesideC.lean: beside), which the seat asks beside its own
testsFit. Where the places' numbers cannot be made it gives nothing.

Main names: beforePointOf, sharedSeatAt.

What is not claimed. That the message which beforePointOf names is the right one: no test here says
which message must be named. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.ProofFile.Lot.K14Seat
import Johnson.Desc.K12.Seat.Fill
import Johnson.Desc.OnPlan.OkBesideC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14
open VerifiableInference.OnPublicFiles

/-- The first chain's message that must be fixed before the shared point is drawn. -/
def beforePointOf (N : H2U.Places4) : List (Nat × Nat) :=
  match ((H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).before.filter fun m => m.1 == 1).map (·.2) with
  | [] => []
  | n :: l => [(1, l.foldl max n)]

/-- The whole shared chain, at the maker's public part. -/
def sharedSeatAt (Z : ProofFile.Pub) : Option ProofFile.SharedSeat :=
  match H2U.placesOfMade Z.made with
  | .ok N =>
    some (sharedSeatOf Z.p.chains (beforePointOf N)
      (fun _ => VerifiableInference.Desc.K12.Seat.tests N) []
      VerifiableInference.Desc.K12.Seat.last (OkD.AtC.beside Z.p.X Z.p.chains))
  | .error _ => none

end Desc.K14
