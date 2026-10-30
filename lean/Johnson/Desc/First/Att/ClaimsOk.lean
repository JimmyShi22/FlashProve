-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/ClaimsOk.lean: kind K5: the claims' tests on the plan alone, as one Bool.

What is asked, in this order: a call that is no softmax-table call has the padding key 0; an index
has at most 16 bits; and all other tests on public numbers of the tables and the runs, by their own
text: `tablesP` and the three runs are run once at a blank record of the place's lengths (every value
0) and must return.
Main names: `blankHeard`, `blankZk`, `blankPts`, `padKeyOk`, `dryOk`, `claimsOk`.
That a test which passes at the blank record passes at every record of these lengths is not shown in
this file or in what it imports. The tables' two tests on values pass at the blank record idly and stay where they are. `claimsOk`
adds to the runs' own tests and replaces none.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.RunsK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open OnBytes.Model (Aff)

def padKeyOk (g : Geo) : Bool := g.calls.all fun c => c.tab == .kfd || c.padKey == 0

def zeros (n : Nat) : Array E := Array.replicate n zeroE

/-- A sumcheck of n variables at which nothing was heard: n challenges and beta, all 0. -/
def blankSum (n : Nat) : VerifiableInference.Desc.Part.MaskedSum.Heard :=
  { start := Aff.ofConst zeroE, target := zeroE, eps := zeroE, claim := zeroE, first := 0, vars := [], r := List.replicate (n + 1) zeroE, sEnd := 0 }

/-- What would have been heard, all zeros, at the place's lengths. The numbers of variables: after OnBytes/Model/AttentionShape.lean:621-638. -/
def blankHeard (g : Geo) : Heard :=
  let (lgk, lt, ldh, lB, lnT) := (g.lgk, g.lt, g.ldh, g.lB, g.lnT)
  { remainders := Array.replicate (g.units .kr [.rm, .rd]).length 0
    scores := g.scores.toArray.map fun u => (0, blankSum (if u.below then lgk + 2 * lnT - 1 + ldh else lgk + lnT + ldh))
    five := 0, bits := 0, two := 0, division := blankSum (lgk + lt), gam := zeros 2, values := 0
    below := blankSum (lgk + 2 * lnT - 1 + lB), on := blankSum (lgk + lnT + lB), point := zeros (2 * lgk + 2 * lt + 4), maxima := 0
    om := zeros g.NP, atIndex := blankSum (lt + lgk + ldh), om' := zeros g.NP, key := blankSum (2 * lt + lgk), om'' := zeros g.NP
    cells := blankSum (lt + lgk + 4) }

/-- Each call's key point, all zeros: as many coordinates as the call has key bits. -/
def blankZk (g : Geo) : Array (Array E) := g.calls.map fun (cc : CallG) => zeros cc.n

/-- What the claims would read, all zeros, at the place's lengths. -/
def blankPts (g : Geo) : Option Pts :=
  let z := Aff.ofConst zeroE
  pointsOf g (blankZk g) (blankHeard g) { scores := Array.replicate g.scores.length z, division := z, below := z, on := z, atIndex := z, key := z, cells := z }

/-- The tables and the three runs return at the blank record. nzx: the length of the lookup's point. -/
def dryOk (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) : Bool :=
  let g := c.geo
  (do
    let p ← blankPts g
    let t ← tablesP g c.mats c.nW { zx := zeros nzx, planesOk := planesOk, phiB0 := zeros (2 ^ g.lmb), phiB1 := zeros (2 ^ g.lmb), phiP := zeros (2 ^ g.lmb) } p
    let i : Runs.In := { g := g, p := p, t := t, zk := blankZk g, iU3 := c.iU3 }
    let f ← Runs.firstRun i K
    let _ ← Runs.keysRun i k3 f.2
    let _ ← Runs.secondRun i K
    pure ()).isSome

/-- **The claims' tests on the plan alone.** -/
def claimsOk (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) : Bool :=
  padKeyOk c.geo && Decidable.decide (c.geo.lt ≤ 16) && dryOk c K k3 planesOk nzx

end VerifiableInference.Desc.First.Att.P
