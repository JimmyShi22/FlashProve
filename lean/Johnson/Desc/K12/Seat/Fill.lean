-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Seat/Fill.lean: what fills the shared chain beside K14's own blocks: the two
proximity tests and the chain's last block, as values.

This file holds definitions only; no theorem is stated.

  tests N     the kind K12's block (its frame, Johnson/Desc/K12/Frame.lean, with its parts joined:
              guardedProximityTestParts, Johnson/Desc/K12/JoinGuarded.lean; the front is its first part) at the places
              ⟨2, none, 9⟩ (the test on G_u) and, where the plan gives numbers for it, ⟨2, none, 10⟩
              (the test on G_omega), each seated by Block.inside (Johnson/Desc/K12/Seat.lean).
              N: the places' numbers off the plan, with the oracle messages' tenants and what must
              be sent before the first draw (placesOfMade and proximityTestParametersAt).
  last front  the chain's end (Johnson/Desc/ChainEnd.lean) at chain 2, piece 11: sealed; nothing is
              left untested; on the plan: the last round that the blocks in front declare counts no
              claims. front: the very blocks that are laid in front of it.
Where the plan gives no numbers for G_omega's test there is no block at piece 10: the file's test of
the blocks' rounds against the plan's is what refuses then, if the plan has such a test.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K12.Seat
import Johnson.Desc.ChainEnd
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Seat
open Desc.K14
open VerifiableInference.Desc (Block)

/-- **The shared chain's two proximity tests.** -/
def tests (N : H2U.Places4) : List (Block St Unit) :=
  [onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U))] ++
    N.O.toList.map fun nO => onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO))

/-- **The shared chain's last block.** -/
def last (front : List (Block St Unit)) : Block St Unit :=
  ChainEnd.chainEnd 2 11 true (front.flatMap (·.rounds)) fun d => ChainEnd.untestedL d.st

end VerifiableInference.Desc.K12.Seat
