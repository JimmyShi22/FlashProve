-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/Makers/K8AsksAtMakers.lean: THE SMALLNESS TEST'S FAMILIES OF TABLES ARE THERE
AND NONE IS EMPTY, AT WHAT THE PUBLIC PART'S MAKERS RETURN AT THE FULL SIZE: proved by evaluation in
Lean's kernel, and carried to the makers' own values.

Why. The first row of the smallness test's lot comes down to one closed test on the public part,
`P1K8L.k8AsksWB` (Johnson/AtFull/Desc/Lots/K8GroundOf.lean): at the head's link, and at the
attention's and the layers' link of each of the twelve groups, the list of families of tables
(Johnson/Desc/First/K8/Asks.lean) is not empty, and no family in it is empty or sums over no row.
That test reads three parts of the public part: the head's shape; the attention's plans (of each its
shape); the layers' public values (the layout and the list of reads).

  `k8AsksLA L A`: the test's second part, with the layers' public values L and the attention's plans
    A as letters. `k8AsksWB_parts`: the test is its part at the head's shape and this one: by
    definition.
  `k8Head_W`: [Lean's kernel; no free letter] the head's part accepts at the typed value of the
    head's shape at the full size (`Cond.hFull`).
  **`k8Asks_W`**: [Lean's kernel; no free letter] at what the makers return
    (`atMakers`, Johnson/AtFull/Public/AtWitnesses.lean) the second part accepts.
  **`k8AsksWB_at`**: so the whole test accepts at a public part with the makers' layers' public
    values and attention's plans and with that head's shape.
Negative tests stand beside it: Johnson/AtFull/Entry/Makers/K8AsksAtMakersNo.lean.

Limits. `OpensAt` and `Makers` are premises, as in AtWitnesses.lean: nothing says here that any
maker returns at any files. The test says that the lists are not degenerate; it does not say that
they are the lists that the links' own routines make. WHAT AN ACCEPT AMOUNTS TO: each of the three
lists ends in three written families, so "not empty" is idle; a power of two is never 0; so an
accept says that twelve attention's plans are there and that numbers of at most seven kinds are not
0: the head's number of parts and of tokens; each attention's number of parts and of tokens; the
layers' two numbers of parts and their number of tokens. The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Public.AtWitnesses
import Johnson.AtFull.Desc.Lots.K8GroundOf
import Johnson.Goal.Meaning.HeadAtFullIs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Entry

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Public (atMakers OpensAt Makers at_witnesses)
open OnBytes.Road.K4.Trial.AttL2 (AOf)
open VerifiableInference.Desc.First (K8.Asks.head K8.Asks.attention K8.Asks.layers)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)

/-- At each group below 12: an attention's plan is there; the attention's and the layers' link's
lists of families are not empty, and no family in them is empty or sums over no row. -/
def k8AsksLA (L : Layer.Pub) (A : Array Attention.Plan) : Bool :=
  (List.range 12).all fun g =>
    (A[g]?).isSome && P1K8L.k8OkL (((A[g]?).map fun P => K8.Asks.attention P.S).getD []) &&
      P1K8L.k8OkL (K8.Asks.layers L.y L.rd g)

/-- The closed test on the public part is its part at the head's shape and `k8AsksLA`. -/
theorem k8AsksWB_parts (W : Verify.Public) :
    P1K8L.k8AsksWB W = (P1K8L.k8OkL (K8.Asks.head W.hS) && k8AsksLA W.layers W.A) := rfl

/-- By the kernel: the head's part accepts at the typed value of the head's shape. -/
theorem k8Head_W : P1K8L.k8OkL (K8.Asks.head Cond.hFull) = true := by decide +kernel

/-- **By the kernel: at what the makers return, the part on the layers' public values and the
attention's plans accepts.** -/
theorem k8Asks_W : atMakers (fun L _ A => k8AsksLA L A) = true := by decide +kernel

variable {y : Layer.Lay} {sc : Layer.Scales} {wsLay : WsLay} {rope : Array Nat}
  {l : List Attention.Line} {ps : List Attention.Plan} {layers : Layer.Pub}
  {G : Array Layer.HPlan2} {seenA : Array SubPlan}

/-- **The closed test accepts at a public part with the makers' values**, under OpensAt and
Makers. -/
theorem k8AsksWB_at (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA) {X : Public}
    (eL : X.layers = layers) (eA : X.A = AOf ps.toArray seenA) (eS : X.hS = Cond.hFull) :
    P1K8L.k8AsksWB X = true := by
  rw [k8AsksWB_parts, eS, eL, eA, Bool.and_eq_true]
  exact ⟨k8Head_W, at_witnesses O M k8Asks_W⟩

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.k8AsksWB_parts
#print axioms Johnson.AtFull.Entry.k8Head_W
#print axioms Johnson.AtFull.Entry.k8Asks_W
#print axioms Johnson.AtFull.Entry.k8AsksWB_at
