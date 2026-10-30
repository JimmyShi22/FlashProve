-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/Part.lean: the honest side of the kind "the batching draw" (K9), in
the form of Honest/Frame.lean. The kind's own text does not hold what the prover sends
(Johnson/Desc/First/Batch/Kind.lean): this file holds it. Definitions with code, and one equation by
`rfl`.

What is sent. One round, "BAT-sigma": the prover sends nothing; the verifier draws one element chi.
The half is a row of one part with one move. The part takes no coin, is handed no stretch of another
part's coins, reads nothing of its input, and hands on what it was handed.

The two stops never stop (shares 0 of 1). At some values of chi the verifier refuses behind the
adding (a coefficient or a weight of the one equation is 0). In this round the prover sends nothing,
so there is no message that it could lack. These values are said by "a fall" (Honest/K9/Fall.lean),
not by a stop. What the prover's later rounds do at such a value is not this part's matter.

  `batPart`     the part, general in the three type letters
  `batHalf`     the kind's half, at K9's own numbers of a place (`K9.Where`)
  `batHalvesAt`, `batHalves`   the halves at all segments: at the places that K9's lot reads off the
                plan (`k9Links`, `k9Where`: Johnson/Desc/ProofFile/Lot/K9.lean): of the places' list
                with their stretches of the declared rounds; and at a public part, of its own list
  `batLot`      the lot's honest side. K10's blocks come out of the same lot: its halves are a
                parameter here, filled where K10's honest side is written (Honest/K10/)
  `batLot_name` the name is the lot's own, at every public part
The simulator beside the part and the side stand in a file of their own (Honest/K9/Side.lean).

Of K9's three places a segment the batching's alone has a round: the one equation's and "shut" have
none, and a place without a round has no half.

Limits. Nothing holds `batHalves` or `batLot`'s halves against the description's blocksInOrder list here, and no line of the toy
runs them (it runs `batHalvesAt`): they want a public part (`Pub`): the frame's `strays`, `lotsLacking` and `chainSteps`
hold them there. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.Frame
import Johnson.Desc.ProofFile.Lot.K9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9

variable {V W X : Type}

/-- **The part**: one round, in which nothing is sent. -/
def batPart : Part V W X :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun _ _ _ => .ok ⟨[], []⟩, fun t => t.own⟩] }

/-- **The kind's half**, at the batching's place. -/
def batHalf : KindHalf VerifiableInference.Desc.K9.Where V W X :=
  fun p => ⟨⟨p.chain, some p.link, p.piece, .K9⟩, [batPart]⟩

/-- The halves at all segments: one for each segment whose numbers the lot can read off the plan. xs: the chain's
places, each with its stretch of the declared rounds (empty at a place without a round) and the roots counted in front
(`k9Stretches`). -/
def batHalvesAt (xs : List (Spot × List Fmt.DeclaredRound × Nat)) : List (Placed V W X) :=
  (k9Links xs).filterMap fun l => (k9Where xs l).map batHalf

/-- At a public part. -/
def batHalves (Z : Pub) : List (Placed V W X) := batHalvesAt (k9Stretches Z)

/-- **The lot's honest side.** closings: K10's halves, whose blocks come out of this lot. -/
def batLot (closings : Pub → Ground → List (Placed V W X)) : HLot V W X :=
  { name := "K9: the batching at the gatherer; each; tests; the closing as three blocks"
    halves := fun Z G => batHalves Z ++ closings Z G }

/-- The name is the lot's own. -/
theorem batLot_name (closings : Pub → Ground → List (Placed V W X)) (Z : Pub) :
    (batLot closings).name = (k9Ninth Z).name := rfl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batPart
#print axioms ProofFile.Honest.K9.batHalf
#print axioms ProofFile.Honest.K9.batHalvesAt
#print axioms ProofFile.Honest.K9.batHalves
#print axioms ProofFile.Honest.K9.batLot
#print axioms ProofFile.Honest.K9.batLot_name
