-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkJoinAt.lean: THE LAW OF A LINK ON THE ROAD OF MOVES, AT THE DRIVER's
SEGMENT: `LinkJoin.AtTheDriver` (Johnson/Desc/First/Link/Law/LinkJoin.lean) IS PROVED,
with a guard.

How. The first half is the shape's law (`Shape.linkAt_shape`). The second half is the joining in
moves (`K9L.inMoves`, Johnson/Desc/First/Batch/Law/JoinMoves.lean), called at b₁ := the segment's
batching, b₂ := the frame's block behind it, b₃ := the first block of its closing.

THE GUARD. `close_three`: the driver's segment closes in THREE blocks. `close_head`: the first of
them is what the record H holds at the place ⟨1, l, n + 3, K9⟩, with that place written. Over a
driver that lays the whole closing as ONE block (the form before this one) `close_three` is false,
and `AtTheDriver`'s second half is empty there: a block with rounds has no yes that is a yes of the
one equation's, which has none. So the two stand beside the law: they do not compile over such a
driver.

Limits. As LinkJoin.lean's. `JoinAsks` itself ties the three pieces to these three blocks (`hpb`,
`hpq`, `hpe`): so the four premises that tie them to the list ps (its blocks are the flat list's;
the three stand at n + 1, n + 2, n + 3) and the one on the closing's head are NOT SPENT by the
proof: they say where in a chain's row the three stand, for whoever splices. AN IMPLICATION:
`JoinAsks` is shown of no record. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.JoinMoves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

/-- **THE LAW OF A LINK ON THE ROAD OF MOVES, AT THE DRIVER's SEGMENT.** -/
theorem atTheDriver : AtTheDriver :=
  fun Cl _ _ _ L h => ⟨Shape.linkAt_shape h,
    fun α W F φ Ok Fu p pw ms₁ ms₂ d N _ _ pb pq pe b₃ on0 on1 on2 on3 tabOf ctx _ _ _ _ _ hJ =>
      K9L.inMoves α W Cl F φ Ok Fu p pw ms₁ ms₂ d N _ L.batchB L.behindB b₃ pb pq pe on0 on1 on2 on3
        tabOf ctx hJ⟩

variable {S' Cl : Type}

/-- **THE GUARD**: the driver's segment closes in three blocks. -/
theorem close_three {H : First.Blocks S' Cl} {l : ℕ} {sub : First.ModelPart} {L : Link S' Cl}
    (h : First.linkAt H l sub = some L) : L.close.length = 3 := by
  have e := congrArg List.length (Shape.linkAt_shape h).2.2.2.1
  simpa [First.closeAddresses, First.closeKinds] using e

/-- The first of the three is what the record holds at the place of the batching kind's block behind
the frame's. -/
theorem close_head {H : First.Blocks S' Cl} {l : ℕ} {sub : First.ModelPart} {L : Link S' Cl}
    (h : First.linkAt H l sub = some L) :
    L.close.head? =
      First.blockAt H ⟨1, some l, (First.kindsBeforeBatching sub (l == 0)).length + 3, .K9⟩ := by
  have e := (Shape.linkAt_shape h).2.2.2.1
  cases hc : L.close with
  | nil =>
    rw [hc] at e
    simp [First.closeAddresses, First.closeKinds] at e
  | cons b r =>
    rw [hc] at e
    simp only [First.closeAddresses, First.closeKinds, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.cons.injEq] at e
    simpa using e.1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.atTheDriver
#print axioms VerifiableInference.Desc.LinkJoin.close_three
#print axioms VerifiableInference.Desc.LinkJoin.close_head
