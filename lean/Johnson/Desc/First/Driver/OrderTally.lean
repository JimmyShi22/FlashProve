-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Driver/OrderTally.lean: a count, for each segment of the first chain, of the
lists of claims and of later steps that the protocol's order names, of those that the segment's
blocks state, and of those that are cut away.

Why. `linkAt` (Johnson/Desc/First/Driver/Chain.lean) lays the protocol's two
orders uncut, and a segment in which a list that an order names is stated by no block is refused on
the plan (Johnson/Desc/First/Driver/OrderLaw.lean). That refusal is one yes or no. This file says
which lists it is about: it takes the same blocks by the same calls as `linkAt` and counts what
`stated` keeps and what it drops.


Main names:
  cutAway: the entries of an order that `stated` drops.
  stated_add_cutAway: every entry of an order is either stated or cut away.
  tallyAt, tally: one line of text for each segment.

Limits. A count, not a test: nothing is refused here. It says which lists no block states; it does
not say who, if anybody, does the work of such a list elsewhere. Nothing on soundness.

-/
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

/-- The entries of an order that `stated` drops: their block is missing or has no list of that
name. -/
def cutAway {B : Type} (names : B → List String) (bs : List B) (order : List (Nat × String)) :
    List (Nat × String) :=
  order.filter fun o => !((bs[o.1]?).any fun b => (names b).contains o.2)

/-- Every entry of an order is either stated or cut away. -/
theorem stated_add_cutAway {B : Type} (names : B → List String) (bs : List B)
    (order : List (Nat × String)) :
    order.length = (stated names bs order).length + (cutAway names bs order).length := by
  unfold stated cutAway
  induction order with
  | nil => rfl
  | cons o t ih =>
    simp only [List.filter_cons]
    cases (bs[o.1]?).any fun b => (names b).contains o.2 <;> simp [ih] <;> omega

variable {S Cl : Type}

/-- One segment's line. It takes the segment's blocks as `linkAt` takes them. `none` if a block is
missing. -/
def tallyAt (H : Blocks S Cl) (l : Nat) (sub : ModelPart) : Option String := do
  let hear ← (addresses (some l) (kindsBeforeBatching sub (l == 0))).mapM (blockAt H)
  let nC : Block S Cl → List String := fun b => b.claims.map (·.1)
  let nA : Block S Cl → List String := fun b => b.after.map (·.1)
  let oC := orderOf sub
  let oA := orderAfterOf sub
  pure (s!"link {l}: lists of claims that the order names {oC.length} · stated by a block " ++
    s!"{(stated nC hear oC).length} · cut away {cutAway nC hear oC} · each stretch whole or " ++
    s!"none {(orderCuts sub).map (wholeOrNone nC hear)} ‖ later steps that the order names " ++
    s!"{oA.length} · stated by a block {(stated nA hear oA).length} · cut away " ++
    s!"{cutAway nA hear oA}")

/-- A line for each segment. -/
def tally (H : Blocks S Cl) (links : List ModelPart) : List String :=
  links.zipIdx.map fun x => (tallyAt H x.2 x.1).getD s!"link {x.2}: a block is missing"

end VerifiableInference.Desc.First
