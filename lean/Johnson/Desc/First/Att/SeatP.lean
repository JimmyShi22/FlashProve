-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/SeatP.lean: K5 (Att/K5AttentionKind.lean) at the first chain's state
(Johnson/Desc/First/State.lean), at every one of its places.

The seat. K5 finds, inside an attention segment, the sub-proof's ledger and the field "rows owed". It
leaves the ledger behind the hearing, nothing owed, and the four records of OnBytes/Model's verifier,
rebuilt purely from what was heard, the lookup's key points and the ledger (Att/ToShort.lean, then
Att/Left.lean's toOwn). That verifier's shape is read by this rebuilding alone.
"Rows owed": the state's own question is asked (S.noneWaits): "some 0" and "none" answer alike.
The place: chain 1, an attention segment, piece 3. `beforeOf`: the commitments that the segment has
sent in front of this place, from two numbers of the plan.
Main names: `seatS`, `beforeOf`, `k5At`.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.State
import Johnson.Desc.First.Att.ToShort
import Johnson.Desc.First.Att.Left
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

/-- The seat. shape: read by the rebuilding alone. -/
def seatS (shape : Attention.Shape) : Seat First.S where
  ledger s := match s.here with
    | .att a => some a.F
    | _ => none
  owed s := if s.noneWaits then none else s.rowsOwed
  lay s h G := match s.here with
    | .att a => a.g.bind fun g => (Short.toOwn shape g.zk (toShort h) G).map fun o =>
      { s with rowsOwed := none, here := .att { a with F := G, planes := some o.planes, scores := some o.scores, d := o.d, x := o.x } }
    | _ => none

/-- The oracle messages number r0, …, r1 − 1 of chain 1. -/
def beforeOf (r0 r1 : Nat) : List (Nat × Nat) := (List.range (r1 - r0)).map fun i => (1, r0 + i)

/-- K5's block at segment l, whose sub-proof is that of group g; no claims yet. -/
def k5At {Cl : Type} (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) :
    Option (VerifiableInference.Desc.Block First.S Cl) :=
  (W.A[g]?).map fun p =>
    attentionKind (seatS p.S) [] { link := l, piece := 3, work := (Params.settingOf W.P.frame).workOf .field .request, own := p.own,
                                   before := before }

end VerifiableInference.Desc.First.Att.P
