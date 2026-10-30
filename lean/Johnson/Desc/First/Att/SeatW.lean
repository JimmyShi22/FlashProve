-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/SeatW.lean: K5 whole, what it hears and what it claims, at the first chain's
state, its claims read off the four records of OnBytes/Model's verifier. A seat's file; no part of
the kind.

`runsW`: four named runs: "first", "keys", "second" (Att/RunsK.lean, seated by Att/SeatC.lean) and,
behind "keys", "join": one line that calls the lookup's own function (Look/K3Runs.lean: joinRun) on
K5's key forms. `k5AtW`: the block; its tests on the plan are the hearing's and the claims'.
For the lookup's run "planes" K5 hands K3's block its two readers (Att/Guest.lean: readersOfPS).
A segment takes the runs in this order: K3 "objects", "guests"; K5 "first", "keys", "join", "second";
K3 "planes". A block that states runs which its segment's order does not name fails that segment's
test on the plan.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatP
import Johnson.Desc.First.Att.Guest
import Johnson.Desc.First.Look.K3Seat
import Johnson.Desc.First.Look.K3Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (K3.joinRun K3.seatCalls)

/-- K5's four named runs at the first chain's state, in the protocol's order. -/
def runsW (A : Attention.Plan) : List (String × (Nat → First.S → Except String (List Aff × First.S))) :=
  (runsPS A).flatMap fun r =>
    if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfPS A))] else [r]

/-- K5's block at segment l, group g, with its claims and their tests on the plan. -/
def k5AtW (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) :
    Option (VerifiableInference.Desc.Block First.S Aff) :=
  (W.A[g]?).map fun p =>
    let b := attentionKind (seatS p.S) (runsW p)
      { link := l, piece := 3, work := (Params.settingOf W.P.frame).workOf .field .request, own := p.own, before := before }
    { b with planOk := b.planOk && claimsOkAt p }

end VerifiableInference.Desc.First.Att.P
