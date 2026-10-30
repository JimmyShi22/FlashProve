-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/Makers/K8AsksAtMakersNo.lean: NEGATIVE TESTS BESIDE `k8Asks_W`
(Johnson/AtFull/Entry/Makers/K8AsksAtMakers.lean), proved by evaluation in Lean's kernel, no free
letter: the public part's makers return at the full size, and at a bent value the test `k8AsksLA`
rejects. So the accept in that file is not due to a maker's error being read as an accept, nor to a
test that accepts everything.

  `k8Asks_no_plan`: with the last attention's plan taken away.
  `k8Asks_no_parts`: with the layers' layout's numbers of parts emptied: a family of the layers'
    link then has no matrix.
  `k8Asks_no_rows`: with the number of tokens in each attention's shape set to 0: a family of the
    attention's link then sums over no row.
  `k8Asks_no_each`: the same at one group alone, for each of the twelve groups in turn: so the test
    reads the attention's shape of every group.
  `k8Head_no`: the head's part, with the number of parts of the head's first matrix in the typed
    value set to 0: its first family then has no matrix.

Limits. Bent values of our own making; they show that the test can fail at these places; of other
places they say nothing. Nothing on soundness.

-/
import Johnson.AtFull.Entry.Makers.K8AsksAtMakers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Entry

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Public (atMakers)
open VerifiableInference.Desc.First (K8.Asks.head)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)

/-- The makers return; with eleven attention's plans the test rejects. -/
theorem k8Asks_no_plan : atMakers (fun L _ A => !k8AsksLA L A.pop) = true := by decide +kernel

/-- The makers return; with no numbers of parts in the layers' layout the test rejects. -/
theorem k8Asks_no_parts :
    atMakers (fun L _ A => !k8AsksLA { L with y := { L.y with parts := #[] } } A) = true := by
  decide +kernel

/-- The makers return; with no token in the attention's shapes the test rejects. -/
theorem k8Asks_no_rows :
    atMakers (fun L _ A => !k8AsksLA L (A.map fun P => { P with S := { P.S with T := 0 } })) =
      true := by decide +kernel

/-- The makers return; with no token in one attention's shape alone the test rejects, whichever of
the twelve groups it is. -/
theorem k8Asks_no_each :
    atMakers (fun L _ A => (List.range 12).all fun g =>
      !k8AsksLA L (A.modify g fun P => { P with S := { P.S with T := 0 } })) = true := by
  decide +kernel

/-- The head's part rejects the typed value with no part of the first matrix. -/
theorem k8Head_no : P1K8L.k8OkL (K8.Asks.head { Cond.hFull with NHf := 0 }) = false := by
  decide +kernel

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.k8Asks_no_plan
#print axioms Johnson.AtFull.Entry.k8Asks_no_parts
#print axioms Johnson.AtFull.Entry.k8Asks_no_rows
#print axioms Johnson.AtFull.Entry.k8Asks_no_each
#print axioms Johnson.AtFull.Entry.k8Head_no
