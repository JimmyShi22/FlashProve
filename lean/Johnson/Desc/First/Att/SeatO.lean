-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/SeatO.lean: kind K5 at the first chain's state, on what K5 itself heard, with
no function of OnBytes/Model that can refuse but the ledger's: the seats, the four named runs of
claims and the block of Att/SeatH.lean, with two turns.

(1) `seatSO`: the hearing's seat lays what was heard (heard5) and the ledger behind the hearing, and
wipes the count of rows owed without comparing it (the block's decision has asked in front, under
"K5.owed", that none waits).
It does not rebuild the four records of OnBytes/Model's verifier (planes,
scores, d, x): these stay as they lay. Nothing on this road reads them.
(2) `seatCO`: the claims' seat takes what the lookup's kind hands in from Att/LookO.lean (lookOfO,
padOfO) where Att/SeatH.lean's takes Att/SeatC.lean's lookOf and padOf.
`keysOfO`, `readersOfO`, `runsO`, `claimsOkAtO`, `k5AtO`: as Att/SeatH.lean's and Att/SeatC.lean's.
A second hearing in one segment is refused ("K5.lay"), and so is a hearing where the lookup has laid
nothing.
Limits: the rebuilding had tests of its own (on lengths; that each list of keys is held by a call);
`seatSO` does not ask them where it lays. What the claims and the tables read is made of heard5 by
Att/RunsK.lean's ptsFrom, with that function's own tests, where a run or the quiet step asks for it.
That the claims' seat, the runs and the test on the plan are those of Att/SeatH.lean, and how the
two hearing's seats part, is Att/SeatOAgrees.lean's.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatH
import Johnson.Desc.First.Att.LookO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (K3.joinRun K3.seatCalls)

/-- The hearing's seat: heard5 and the ledger are laid; the four records are not rebuilt. -/
def seatSO : Seat First.S where
  ledger s := match s.here with
    | .att a => some a.F
    | _ => none
  owed s := if s.noneWaits then none else s.rowsOwed
  lay s h G := match s.here with
    | .att a => a.g.bind fun _ =>
      (First.S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } h).toOption
    | _ => none

/-- The claims' seat. -/
def seatCO (c : ParC) : SeatC First.S where
  pts s := match s.here with
    | .att a => a.g.bind fun g => s.heard5?.bind fun h => ptsFrom c.geo g.zk h a.F
    | _ => none
  cols s := match s.here with | .att a => (a.F.trees[c.iU3]?).map (·.K) | _ => none
  look s := match s.here with | .att a => a.g.map (lookOfO c.geo.lmb) | _ => none
  pad s := match s.here with | .att a => a.g.map fun g => padOfO g.shape | _ => none
  zk s := match s.here with | .att a => a.g.map (·.zk) | _ => none

def keysOfO (A : Attention.Plan) (s : First.S) : Option (Array Aff) :=
  keysOfK (seatCO (parCOf A)) (parCOf A) s
def readersOfO (A : Attention.Plan) (s : First.S) :
    Option ((Nat → Nat → Option Aff) × (Nat → Option Aff)) :=
  readersOfK (seatCO (parCOf A)) (parCOf A) s

/-- K5's four named runs. -/
def runsO (A : Attention.Plan) :
    List (String × (Nat → First.S → Except String (List Aff × First.S))) :=
  (runsK (seatCO (parCOf A)) (parCOf A)).flatMap fun r =>
    if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A))]
    else [r]

/-- The claims' tests on the plan alone. K: out of the planned ledger. -/
def claimsOkAtO (A : Attention.Plan) : Bool :=
  claimsOk (parCOf A) (((A.seam.Fp.trees[A.iU3]?).map (·.K)).getD 0) (padOfO A.fs)
    (Look.planesOk A.fs A.S.cf.lmb) (A.fs.dT)

/-- K5's block at segment l, group g. -/
def k5AtO (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) :
    Option (VerifiableInference.Desc.Block First.S Aff) :=
  (W.A[g]?).map fun p =>
    let b := attentionKind seatSO (runsO p)
      { link := l, piece := 3, work := (Params.settingOf W.P.frame).workOf .field .request
        own := p.own, before := before }
    { b with planOk := b.planOk && claimsOkAtO p }

end VerifiableInference.Desc.First.Att.P
