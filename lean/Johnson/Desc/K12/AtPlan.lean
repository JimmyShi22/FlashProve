-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/AtPlan.lean: the numbers of a proximity test's place as the kind's parameter `P12`
(Johnson/Desc/K12/Frame.lean), off the plan. Definitions only, all computable; nothing is proved
here.

  `proximityTestParametersAt place x`   a place's numbers (`H2U.PlaceNums`, Plan/PlaceOfPlan.lean) as a `P12`: the
                    numbers; the codes' numbers; the oracle messages with their tenants
                    (`testOracles5`); `before` (`beforeOf`); the answers to a sample; whether the
                    masks ride. Where the caller's place names another chain than the numbers do,
                    and where the numbers give no declared rounds: `noP12`.
  `noP12 place`     a `P12` without a stage: at it `proximityTestKind` makes the block whose test on the plan
                    fails.
  `p12OfMade m`     the first chain's last test (place ⟨1, none, 2, .K12⟩), from what the planner
                    and `sendsOf` make of the three public files.
  `p12FoldedOfMade m piece`, `p12OmegaOfMade m piece`, `p12OwnOfMade m piece`: the other three
                    places of a proof file (chains 2, 2 and 3). piece: the block's number on its
                    chain, the caller's to say.
All four are total: where the plan gives no numbers they give `noP12`: a loud no on the plan, never
an empty seat.

Limits. Those of Plan/PlaceOfPlan.lean. The namespace is H2U, under which the files that stand on
this one name it. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Frame
import Johnson.Desc.K12.TestOracles
import Johnson.Desc.K12.Plan.PlaceOfPlan

set_option autoImplicit false
namespace H2U
open VerifiableInference.Desc VerifiableInference.Desc.K12 Johnson.G.OfPlan

def noP12 (place : Place) : P12 :=
  { place := place,
    nums :=
      { rows := 0, work := 0, stages := [], ownMask := false, first := [], free := 0,
        firstTree := 0 },
    idx := [], oracles := [], before := [], answers := 0, early := false }

def proximityTestParametersAt (place : Place) (x : PlaceNums) : P12 :=
  if place.chain != x.chain then noP12 place else
  match testOracles5 x.nums x.firstGroup with
  | some os =>
    { place := place, nums := x.nums, idx := x.idx, oracles := os,
      before := beforeOf x.chain x.nums, answers := x.answers, early := x.early }
  | none => noP12 place

/-- **The first chain's last test.** -/
def p12OfMade (m : Made) : P12 :=
  let place : Place := ⟨1, none, 2, .K12⟩
  match placesOfMade m with
  | .ok Ps => proximityTestParametersAt place Ps.L
  | .error _ => noP12 place

/-- **The folded row's test**, on the shared chain; piece: its block's number there. -/
def p12FoldedOfMade (m : Made) (piece : Nat) : P12 :=
  let place : Place := ⟨2, none, piece, .K12⟩
  match placesOfMade m with
  | .ok Ps => proximityTestParametersAt place Ps.U
  | .error _ => noP12 place

/-- **Omega's test**, on the shared chain. Where the plan has no such test: noP12. -/
def p12OmegaOfMade (m : Made) (piece : Nat) : P12 :=
  let place : Place := ⟨2, none, piece, .K12⟩
  match placesOfMade m with
  | .ok Ps => (Ps.O.map (proximityTestParametersAt place)).getD (noP12 place)
  | .error _ => noP12 place

/-- **The request's own test**, on the last chain. -/
def p12OwnOfMade (m : Made) (piece : Nat) : P12 :=
  let place : Place := ⟨3, none, piece, .K12⟩
  match placesOfMade m with
  | .ok Ps => proximityTestParametersAt place Ps.W
  | .error _ => noP12 place

end H2U
