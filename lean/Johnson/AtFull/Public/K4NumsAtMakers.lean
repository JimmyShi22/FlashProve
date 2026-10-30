-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/K4NumsAtMakers.lean: THE FIFTEEN NUMBERS THAT THE ROUNDS OF K4's SUB-PROTOCOL
READ OF THE LAYERS' PUBLIC PARAMETERS AND OF A GROUP's PLAN (numsOf,
Johnson/AtFull/Rounds/K4Nums.lean) ARE THE WRITTEN ONES (numsW, the same file) AT ALL TWELVE GROUPS:
by Lean's kernel at what the public part's makers return, and carried to the witnesses by
at_witnesses (Johnson/AtFull/Public/AtWitnesses.lean).

  `k4NumsB w L G`: at each group below 12 there is a plan, and its fifteen numbers are w g.
  `k4Nums_W`: [Lean's kernel; no free letter] atMakers accepts k4NumsB numsW.
  `k4Nums_no`: a negative test: against numsW with its ninth number (lamS) raised by one the makers
    return and the test rejects.
  **`k4Nums_at`**: under OpensAt and Makers: at each g below 12 and each plan hp that stands at g in
    the witnesses' G: numsOf layers hp = numsW g.

Limits. OpensAt and Makers are premises, as in AtWitnesses.lean. The written numbers are
K4Nums.lean's; whence they come is that file's to say. The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Public.AtWitnesses
import Johnson.AtFull.Rounds.K4Nums

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Rounds (numsOf numsW)

/-- At each group below 12: a plan, and its fifteen numbers are w g. -/
def k4NumsB (w : Nat → List Nat) (L : Layer.Pub) (G : Array Layer.HPlan2) : Bool :=
  (List.range 12).all fun g => (G[g]?).any fun hp => decide (numsOf L hp = w g)

/-- **By the kernel: at what the makers return, the fifteen numbers are the written ones at all
twelve groups.** -/
theorem k4Nums_W : atMakers (fun L G _ => k4NumsB numsW L G) = true := by decide +kernel

/-- A negative test: the makers return, and against the written list with its ninth number raised
by one the test rejects. -/
theorem k4Nums_no :
    atMakers (fun L G _ => !k4NumsB (fun g => (numsW g).set 8 ((numsW g).getD 8 0 + 1)) L G) =
      true := by decide +kernel

variable {y : Layer.Lay} {sc : Layer.Scales} {wsLay : WsLay} {rope : Array Nat}
  {l : List Attention.Line} {ps : List Attention.Plan} {layers : Layer.Pub}
  {G : Array Layer.HPlan2} {seenA : Array SubPlan}

/-- **The fifteen numbers at the witnesses**, under OpensAt and Makers. -/
theorem k4Nums_at (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA) :
    ∀ g, g < 12 → ∀ hp, G[g]? = some hp → numsOf layers hp = numsW g := by
  intro g hg hp e
  have h := at_witnesses O M k4Nums_W
  have hg' := List.all_eq_true.1 h g (List.mem_range.2 hg)
  rw [e] at hg'
  exact of_decide_eq_true hg'

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.k4Nums_W
#print axioms Johnson.AtFull.Public.k4Nums_no
#print axioms Johnson.AtFull.Public.k4Nums_at
