-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Points.lean: the honest prover's side of an attention segment's own rounds:
the named points and weights, made of the challenges BY THE VERIFIER's OWN TEXT. Definitions with
code; no theorem.

The verifier cuts each lookup call's key point and its own challenges into named points in one
function, `pointsOf` (Johnson/Desc/First/Att/Points.lean), which reads what it has heard
(`Heard`, Att/K5Heard.lean). The prover needs the same points earlier, while some challenges are
still to come, and it needs a sumcheck's weights and maps at points that are not yet challenges. So
here the challenges so far are laid into a `Heard` whose other fields are blank, and the verifier's
function is called on it. So no cut of a key point or of a sumcheck's challenges is typed a second
time. That function's result does not hold the batching elements' powers, nor three of the five cuts
of the round that draws many elements: a caller reads these off `heardAt`'s fields.

  `sumAt`      a sumcheck of which only the variables' challenges are laid
  `heardAt`    what was heard so far, in the verifier's own type; `over` lays another point in the
               place of one sumcheck's challenges
  `ptsAt`      the verifier's named points and weights at that
  `ptsOf`      the same with nothing laid over

What is blank. Every number of a scalar is 0, every row that a sumcheck leaves is the form 0, every
sumcheck's start, target, eps and claim are 0. None of the fields that the honest side reads depends
on these: it reads points, pieces' weights and tile weights alone. A challenge that has not been
heard reads as 0, at the right length; the elements of the round that draws many are none until it
is heard.

Limits. `ptsAt` returns nothing where the verifier's function refuses: its tests are on lengths
alone. Tests: Johnson/Desc/K5/Honest/PointsToy.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Faces
import Johnson.Desc.First.Att.ClaimsOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E zeroE)
open OnBytes.Model (Aff)
open VerifiableInference.Desc.First.Att.P (Heard Left Pts pointsOf blankSum)
open VerifiableInference.Desc.Part (MaskedSum.Heard)

/-- A sumcheck of which only the challenges of the variables' rounds are laid. The verifier's `chal`
drops the last entry, the challenge of the further variable: a 0 stands there. -/
def sumAt (r : Array E) : MaskedSum.Heard := { blankSum 0 with r := r.toList ++ [zeroE] }

/-- **What was heard so far, in the verifier's own type.** over p: a point to lay in the place of
the challenges of the sumcheck that is part p. -/
def heardAt (P : Pub5) (c : Chal) (over : Nat → Option (Array E)) : Heard :=
  let x := P.x
  let r (p : Nat) : MaskedSum.Heard := sumAt ((over p).getD (c.r x p))
  let pw (p : Nat) (n : Nat) : Array E := powers (c.one (firstOf x p)) n
  { remainders := Array.replicate x.planeMessages 0
    scores := (Array.range x.score.length).map fun p => (0, r p)
    five := 0, bits := 0, two := 0, division := r (iSE x), gam := pw (iGam x) 2, values := 0
    below := r (iVM x), on := r (iVD x), point := c.many (firstOf x (iZero x)), maxima := 0
    om := pw (iM6 x) x.pairs, atIndex := r (iSF x), om' := pw (iOm4 x) x.pairs, key := r (iSD x)
    om'' := pw (iOm5 x) x.pairs, cells := r (iHB x) }

/-- The rows that the sumchecks leave, all the form 0. -/
def blankLeft (n : Nat) : Left :=
  let z := Aff.ofConst zeroE
  { scores := Array.replicate n z, division := z, below := z, on := z, atIndex := z, key := z
    cells := z }

/-- **The verifier's named points and weights**, at the challenges so far. -/
def ptsAt (P : Pub5) (c : Chal) (over : Nat → Option (Array E)) : Option Pts :=
  pointsOf P.g c.zk (heardAt P c over) (blankLeft P.x.score.length)

/-- The same with nothing laid over. -/
def ptsOf (P : Pub5) (c : Chal) : Option Pts := ptsAt P c fun _ => none

/-- One point laid over: part p's. -/
def only (p : Nat) (r : Array E) (p' : Nat) : Option (Array E) := if p' == p then some r else none

end H2K5.Honest
