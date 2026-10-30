-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/SeatH.lean: K5 whole at the first chain's state, its claims made of what K5 itself
heard (the state's field heard5). A seat's file; no part of the kind.

Main names:
  `seatSH`: Att/SeatP.lean's seat, which also lays what was heard into heard5. A second hearing in one
    segment is refused ("K5.lay"). The four records of OnBytes/Model's verifier are still laid.
  `seatCH`: the claims' seat: what the claims read is `ptsFrom` of heard5, the lookup's key points and
    the ledger as it stands. The four records are not read.
  `keysOfH`, `readersOfH`, `runsH`, `k5AtH`: as Att/SeatW.lean's, over these two seats.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (K3.joinRun K3.seatCalls)

/-- The hearing's seat: both are laid. -/
def seatSH (shape : Attention.Shape) : Seat First.S :=
  let t := seatS shape
  { t with
    lay := fun s h G => (t.lay s h G).bind fun s' => (s'.hear5? h).toOption }

/-- The claims' seat: the kind's own road. -/
def seatCH (c : ParC) : SeatC First.S :=
  { seatCS c with
    pts := fun s => match s.here with
      | .att a => a.g.bind fun g => s.heard5?.bind fun h => ptsFrom c.geo g.zk h a.F
      | _ => none }

def keysOfH (A : Attention.Plan) (s : First.S) : Option (Array Aff) := keysOfK (seatCH (parCOf A)) (parCOf A) s
def readersOfH (A : Attention.Plan) (s : First.S) : Option ((Nat → Nat → Option Aff) × (Nat → Option Aff)) :=
  readersOfK (seatCH (parCOf A)) (parCOf A) s

/-- K5's four named runs, on the kind's own road. -/
def runsH (A : Attention.Plan) : List (String × (Nat → First.S → Except String (List Aff × First.S))) :=
  (runsK (seatCH (parCOf A)) (parCOf A)).flatMap fun r =>
    if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfH A))] else [r]

/-- K5's block at segment l, group g. -/
def k5AtH (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) :
    Option (VerifiableInference.Desc.Block First.S Aff) :=
  (W.A[g]?).map fun p =>
    let b := attentionKind (seatSH p.S) (runsH p)
      { link := l, piece := 3, work := (Params.settingOf W.P.frame).workOf .field .request, own := p.own, before := before }
    { b with planOk := b.planOk && claimsOkAt p }

end VerifiableInference.Desc.First.Att.P
