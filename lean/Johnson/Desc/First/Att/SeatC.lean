-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/SeatC.lean: the claims' seat (Att/RunsK.lean: SeatC) at the first chain's state
(Johnson/Desc/First/State.lean), read off the four records of OnBytes/Model's verifier that the
state's part for an attention segment holds. A seat's tool; no part of the kind.

Main names:
  `ptsOfOwn`: these four records as the kind's `Pts`, field for field; a sumcheck's row is the one laid
    in its record.
  `lookOf`, `padOf`: what the lookup hands on, made by OnBytes/Model's functions on its record.
  `parCOf`: the place's numbers out of OnBytes/Model's plan of the sub-proof.
  `seatCS`, `runsPS`, `keysOfPS`, `claimsOkAt`: the seat; the runs and the key forms at it; the claims'
    tests on the plan at a plan.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.State
import Johnson.Desc.First.Att.ClaimsOk
import Johnson.Desc.First.Att.GeoOf
import OnBytes.Model.Attention

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Attention

def w1Of (v : Array PW) : Array W1 := v.map fun x => { lam := x.lam, a := x.a, wp := x.wp }
def sum3Of (o : Sc3) : SumP := { r := o.r, ends := o.sEnd, row := o.rowU }
def sumDOf (o : Scd) : SumP := { r := o.r, ends := o.sEnd, row := o.rowU }

def ptsOfOwn (planes : Array PlaneClaim) (scores : Array Score) (d : Divide) (x : Attain) : Pts :=
  { planes := planes.map fun c => { call := c.call, z := c.z, isD := c.isD, pw := w1Of c.pw, s0 := c.s0, np := c.np }
    scores := scores.map fun k => { call := k.call, claim := k.claim, below := k.seg == Seg.fm, pw := w1Of k.pw, zg := k.zg, zs := k.zs, zi := k.zi, zj := k.zj, wI := k.wI, s0 := k.s0, sc := sum3Of k.sc }
    d := { pwW := w1Of d.pwW, pwX := w1Of d.pwX, pwH := w1Of d.pwH, qWH := d.qWH, zsl := d.zsl, zgW := d.zgW, ziW := d.ziW, zcW := d.zcW, zgX := d.zgX, ziX := d.ziX, zgH := d.zgH, ziH := d.ziH, zcH := d.zcH
           s5 := d.s5, sIB := d.sIB, s5h := d.s5h, scE := sum3Of d.scE, gam := d.gam, sCl := d.sCl, vpm := sum3Of d.vpm, wJv := d.wJv, vpd := sum3Of d.vpd }
    x := { tg := x.tg, ti := x.ti, sM6 := x.sM6, scF := sum3Of x.scF, scd := sumDOf x.scd, scH := sum3Of x.scH } }

def lookOf (lmb : Nat) (g : Model.Forest.Heard) : LookIn :=
  { zx := g.zx, planesOk := (Model.Forest.planeCols g.shape lmb).toBool, phiB0 := (Model.Forest.phiB g lmb 0).getD #[]
    phiB1 := (Model.Forest.phiB g lmb 1).getD #[], phiP := Model.Forest.phiP lmb }

def padOf (h : Model.Forest.Shape) : Runs.PadIn :=
  { pub := h.pub, noPub := Model.Forest.noPub h, pubRun := fun l q a b => (Model.Forest.pubRun h l q a b).toOption }

def parCOf (A : Plan) : ParC := { geo := geoOf A.S, iU3 := A.iU3, nW := A.nW, mats := A.mats.map fun M => (M.m, M.k) }

/-- The claims' seat at the first chain's record. -/
def seatCS (c : ParC) : SeatC First.S where
  pts s := match s.here with
    | .att a => a.planes.bind fun planes => a.scores.map fun scores => ptsOfOwn planes scores a.d a.x
    | _ => none
  cols s := match s.here with | .att a => (a.F.trees[c.iU3]?).map (·.K) | _ => none
  look s := match s.here with | .att a => a.g.map (lookOf c.geo.lmb) | _ => none
  pad s := match s.here with | .att a => a.g.map fun g => padOf g.shape | _ => none
  zk s := match s.here with | .att a => a.g.map (·.zk) | _ => none

/-- K5's three named runs at the first chain's record. -/
def runsPS (A : Plan) : List (String × (Nat → First.S → Except String (List Model.Aff × First.S))) := runsK (seatCS (parCOf A)) (parCOf A)

/-- The key forms for the lookup's join, at the first chain's record. -/
def keysOfPS (A : Plan) (s : First.S) : Option (Array Model.Aff) := keysOfK (seatCS (parCOf A)) (parCOf A) s

/-- The claims' tests on the plan alone, at the numbers of OnBytes/Model's plan. K: out of the planned ledger. -/
def claimsOkAt (A : Plan) : Bool :=
  claimsOk (parCOf A) (((A.seam.Fp.trees[A.iU3]?).map (·.K)).getD 0) (padOf A.fs) (Model.Forest.planeCols A.fs A.S.cf.lmb).toBool (A.fs.dT)

end VerifiableInference.Desc.First.Att.P
