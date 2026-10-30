-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Chains23.lean: a key file's shared and third chain, made of the kinds' own blocks.
Definitions with code; no theorem.

  the shared chain: a front block with its share of the tests on the plan; the six blocks of the
  test on the table and the two sendings (`Desc.K14.blocksOr`); the proximity tests on the folded
  row's group and on Omega's (`K12.Seat.onGu`, `onGomega`, of `proximityTestKind guardedProximityTestParts`); the chain's end.
  the third chain: the second part of the test on the table; the taken trees' sources; the proximity
  test on the own group; the chain's end (`Third.lastChainWithOwnTest`).

Main names.
  `sharedPar`, `thirdPar`: the places' parameters, out of the planner's record for the key (setting,
  codes, one-time values).
  `sharedFrontClauses`, `sharedFrontOk`, `sharedFront`: six tests on the plan, by name, and the
  block without a round that asks them.
  `beforeSharedPoint`: which messages must be fixed before the shared point is drawn, off the plan.
  `sharedTests`, `ownTest`: the proximity tests' blocks at their places' numbers.
  `sharedChain`, `thirdChain`: the two chains.

Limits. The blocks are other files' texts; here they are laid in a row. The proximity tests' block
is `proximityTestKind guardedProximityTestParts`, of which that kind's law speaks. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.Key.Places
import Johnson.Desc.K14.Blocks
import Johnson.Desc.K12.Seat.Fill
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.K12.Seat.Own
import Johnson.Desc.Third.Chain
import Johnson.Desc.Third.Border

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open VerifiableInference.Desc (FileDescription Chain Block named need roundlessBlock)
open VerifiableInference.Desc.Third (S₃)

/-! ## The shared chain -/

/-- The place's parameters out of the planner's chains, at the key. The item: a shared chain's
statement's item 0 holds the table's root (Params.Shared.statement). -/
def sharedPar (c : Model.Verify.Chains) (beforePoint : List (Nat × Nat)) : _root_.Desc.K14.P14 :=
  let z := c.made.sized.key
  { set := z.set, scope := if z.once.lines.oneTime then .once else .shared, codes := z.codes,
    S := z.once.shape, item := 0, beforePoint := beforePoint }

/-- The shared chain's front's share of the tests on the plan, at the key's records: six clauses by
name. -/
def sharedFrontClauses (c : Model.Verify.Chains) : List (String × Bool) :=
  let z := c.made.sized.key
  [("one answer to a sample", c.key.shared.given.plan.samples == 1),
   ("the test on the table can be sized", (Params.linSizeOf z.codes z.once).isSome),
   ("the shape read back is the planner's", decide (z.once.shape = c.key.shared.lin)),
   ("the codes read back are the planner's", decide (z.codes = c.key.shared.codes)),
   ("the samples read back are the setting's", z.set.samples == c.key.shared.given.plan.samples),
   ("the plan made anew is the plan read back",
     match Params.sharedPlan z.set z.codes z.once with
     | .ok P => decide (P.plan.entries = c.key.shared.given.plan.entries)
     | .error _ => false)]

/-- All six hold. -/
def sharedFrontOk (c : Model.Verify.Chains) : Bool := (sharedFrontClauses c).all (·.2)

/-- The shared chain's front: a block without a round that asks them. -/
def sharedFront (c : Model.Verify.Chains) : Block _root_.Desc.K14.St Unit :=
  { roundlessBlock "the shared chain's front" 2 none 0 .ok with planOk := sharedFrontOk c }

/-- What must be fixed before the shared point is drawn. -/
def beforeSharedPoint (N : LaterPlaces) : List (Nat × Nat) :=
  (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).before.filter fun x => x.1 == 1

/-- The two proximity tests (as `tests` of Johnson/Desc/K12/Seat/Fill.lean, at these places'
numbers). -/
def sharedTests (N : LaterPlaces) : List (Block _root_.Desc.K14.St Unit) :=
  [VerifiableInference.Desc.K12.Seat.onGu
    (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9,
                                                           .K12⟩ N.U))] ++
  N.O.toList.map fun nO => VerifiableInference.Desc.K12.Seat.onGomega
    (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10,
                                                           .K12⟩ nO))

/-- **The key file's shared chain.** -/
def sharedChain (c : Model.Verify.Chains) (N : LaterPlaces) : Chain _root_.Desc.K14.St Unit :=
  let inFront := _root_.Desc.K14.blocksOr (sharedPar c (beforeSharedPoint N)) ++ sharedTests N
  { first := sharedFront c, front := [], links := [], back := inFront, last :=
      VerifiableInference.Desc.K12.Seat.last inFront }

/-! ## The last chain -/

/-- The parameters of the second part of the test on the table, at the key. -/
def thirdPar (c : Model.Verify.Chains) : VerifiableInference.Desc.Third.P₁₄ :=
  let z := c.made.sized.key
  VerifiableInference.Desc.Third.p₁₄Z z.set z.codes z.once

/-- The proximity test on the own group, at its place's numbers. -/
def ownTest (N : LaterPlaces) : Block S₃ Unit :=
  VerifiableInference.Desc.K12.Seat.onOwn
    (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2,
                                                           .K12⟩ N.W))

/-- **The key file's third chain.** -/
def thirdChain (c : Model.Verify.Chains) (N : LaterPlaces) : Chain S₃ Unit :=
  VerifiableInference.Desc.Third.lastChainWithOwnTest (thirdPar c) (ownTest N)

end VerifiableInference.Desc.Key
