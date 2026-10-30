-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PublicX.lean: TESTS WITH CODE ON PUBLIC PARAMETERS. Four
definitions, and one equation by unfolding. No theorem on any protocol.

What is here. Tests on the public parameters of K4, the sub-protocol of the feed-forward layers' own
rounds: functions into Bool. What the tests are for is said in Law/HearsShape.lean, which imports
this file, and in Law/PublicOne.lean, which stands over it.

  `k4ShapeB p`   FIVE TESTS ON THE PLAN: the host's count of the padding keys is the layout's (the
      host: the sub-protocol that calls the lookup) · each call's factor in the join is there, at
      the array and the places that the plan names · the planes' columns at the plan's shape ·
      la ≤ dT · the shape's calls are as many as the layout's.
  `k4PublicB p`   at one member's parameters: ten comparisons of the plan's numbers (`planNumsB`) ·
      the pure functions that the sub-protocol's hearing calls return (`hearPB`) · `k4ShapeB` · the
      slots that the lookup and the hearing take are at most the plan's number of slots · lt ≤ dT.
  `parAt P hp g`, `k4PublicB_reads`   the test reads the public numbers, the plan and the group
      alone.
  `k4PublicX X`   **that test at each group below 12, at the group's plan**: it reads X.layers and
      X.G alone. To evaluate: ask Lean's evaluator for `k4PublicX X`.

Called. `planNumsB` (Johnson/Desc/First/K4/Returns/Needs.lean), `k4Takes` (Returns/Whole.lean beside
it), `joinB` (Returns/JoinB.lean), `hearPB` (Returns/Pub/JoinPoints.lean), `tablesAt`
(Returns/Pub/Tables.lean), `laidLayers` (Johnson/Desc/First/Look/Laid.lean), and the library's
`Forest.planeCols` and `Forest.elems`.

Kin. `publicX_head` (Law/DearX.lean) has `k4PublicX` true at the public parameters of the hypothesis
on the public files, `P5J.AtMgA`. The short name parAt is borne by other definitions of the library
too, each in a namespace of its own; among them those of Johnson/Desc/First/Att/Row/K5RowBlock.lean,
Honest/K5/Law/Member.lean, Johnson/Desc/ProofFile/Lot/K11.lean and
Johnson/Desc/K10/Honest/CarryTests.lean: whoever opens two of these namespaces whole meets an
ambiguity.

Not shown here. THAT A TEST IS TRUE ANYWHERE (for `k4PublicX`: see Kin). An evaluation at given
public parameters is a test that can fail; it gives no term of Lean. This file evaluates nothing.
NO TEST TRIES `k4PublicX` ITSELF: of these writers' files three more name it in their code
(Law/DearX.lean, Law/PublicOne.lean, Law/LookJoin.lean), and none of the three holds an #eval or a
#guard. THE BOUND 12 IN `k4PublicX`
IS THE FULL SIZE's NUMBER OF GROUPS: at public parameters with fewer groups the test is false for
want of a plan; WITH MORE IT IS SILENT ON EVERY GROUP FROM 12 ON. How long the evaluation runs at a
model's size is not measured here. Following import lines, and stopping unopened at every module
under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name
begins Cb.Bridge, its imports reach none of these; none of the modules that it reaches has
RecCompile in its name, and NONE LIES UNDER Johnson/Desc/ProofFile/ (so nothing of Honest/ and
nothing of its Thread/). Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.First.K4.Returns.Pub.JoinPoints
import Johnson.Desc.First.K4.Returns.Pub.Tables
import Johnson.Desc.First.K4.Returns.JoinB
import Johnson.Desc.First.Look.Laid
import Johnson.Desc.First.K4.Returns.Needs
import OnBytes.Model.VerifyPublic
import Johnson.Desc.First.K4.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Rt (k4Takes planNumsB joinB)
open OnBytes.Desc.First.K4.RtPub (hearPB tablesAt)
open VerifiableInference.Desc.First.Look (laidLayers)

/-- **Five tests on the plan alone.** The second is true where the plan names no array or no places
(`all`, twice): inside `k4PublicB` the test `hearPB` asks that both are there. -/
def k4ShapeB (p : Par) : Bool :=
  (laidLayers p.P == some p.P.y.fo.pub) &&
    ((p.hp.tl.ix.U.getD 2 none).all fun iU3 =>
      (tablesAt p.P p.g).all fun r => joinB p.P p.hp p.g iU3 r.1) &&
    (OnBytes.Model.Forest.planeCols p.P.y.fo p.P.y.h.lmb).toBool &&
    decide (p.P.y.h.la ≤ p.P.y.fo.dT) && (p.P.y.fo.calls.size == p.P.y.calls.size)

/-- **The tests on the plan at one member's parameters, as one.** -/
def k4PublicB (p : Par) : Bool :=
  planNumsB p.P p.hp p.g && hearPB p.P p.hp p.g && k4ShapeB p &&
    decide (Forest.elems p.P.y.fo + k4Takes p.P p.hp p.g ≤ p.hp.ns) &&
    decide (p.P.y.h.lt ≤ p.P.y.fo.dT)

/-- Parameters with the given public numbers, plan and group; the other fields are read by no test
here. -/
def parAt (P : Layer.Pub) (hp : HPlan2) (g : Nat) : Par :=
  { name := "", link := 2 * g, piece := 3, before := [], P := P, hp := hp, g := g }

/-- The test reads the public numbers, the plan and the group alone. -/
theorem k4PublicB_reads (p : Par) : k4PublicB p = k4PublicB (parAt p.P p.hp p.g) := rfl

/-- **THE TEST ON THE PUBLIC PARAMETERS**: at each group below 12, at the group's plan. False where
a group has no plan. 12 is the full size's number of groups: a group from 12 on is not tested. -/
def k4PublicX (X : Verify.Public) : Bool :=
  (List.range 12).all fun g => (X.G[g]?).any fun hp => k4PublicB (parAt X.layers hp g)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4ShapeB
#print axioms ProofFile.Honest.K4.k4PublicB
#print axioms ProofFile.Honest.K4.parAt
#print axioms ProofFile.Honest.K4.k4PublicB_reads
#print axioms ProofFile.Honest.K4.k4PublicX
