-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/PendOfAll.lean: THE PREMISE «pendB AT THE UNIT OF THE CLAIM THAT THE
VERIFIER's STATE HOLDS» OF `merge_makes_row` (Johnson/Top/H0/MergeLaw/RowReturns.lean) FALLS TO ONE
CLOSED TEST ON THE PLANNER's NUMBERS: `pendB` at every unit of the layout. A definition with code,
and theorems with their proofs: calls.

  `unit_of_shape`: a claim that passes the program's test on its sizes (`wsClaimShape`) names a unit
    of the layout.
  **`pend_of_all`**: where `pendB P.lay [ui] 1 lin` says yes at every ui below the number of units,
    and the merge's step accepts at s: `pendB` says yes at the unit of the claim that s holds.
  `pendAllB lay lin`: THE CLOSED TEST, WITH CODE: IT CAN FAIL. `pendAll_says`: what its yes says.
  `merge_makes_row_of_all`: so the merge's accepting step makes `hasRow` at the head from that test
    and an entry of the index masks' ledger behind.
Limits. That the test says yes is shown nowhere here. (Evaluated by Lean's evaluator at the stored
full-size example's public parameter files: yes at 386 of 386 units: a sheet, no proof.) The
ledger's entry stays a premise. No soundness is claimed.

-/
import Johnson.Top.H0.MergeLaw.RowReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model OnBytes.Flat
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- A claim that passes the test on its sizes names a unit of the layout. -/
theorem unit_of_shape {lay : WsLay} {c : WsClaim} (h : wsClaimShape lay c = .ok ()) :
    c.ui < lay.U.size := by
  by_contra hlt
  have hu : lay.U[c.ui]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hlt)
  unfold wsClaimShape at h
  simp [hu, throw, throwThe, MonadExceptOf.throw] at h

/-- **The premise at the state's claim, from the test at every unit.** -/
theorem pend_of_all (P : HeadMergeP) (lin : Params.LinShape)
    (hall : ∀ ui, ui < P.lay.U.size → pendB P.lay [ui] 1 lin = true) {s s' : S}
    {rs : List Fmt.RoundView} (h : headMergeDecide P s rs = .ok s') :
    ∀ a claim, s.here = .head a → a.claim = some claim → pendB P.lay [claim.ui] 1 lin = true :=
  fun a claim ha hcl => hall claim.ui (unit_of_shape (shape_of_yes h a claim ha hcl))

/-- **The closed test on the planner's numbers.** -/
def pendAllB (lay : WsLay) (lin : Params.LinShape) : Bool :=
  (List.range lay.U.size).all fun ui => pendB lay [ui] 1 lin

theorem pendAll_says {lay : WsLay} {lin : Params.LinShape} (h : pendAllB lay lin = true) :
    ∀ ui, ui < lay.U.size → pendB lay [ui] 1 lin = true := fun ui hui =>
  List.all_eq_true.1 h ui (List.mem_range.2 hui)

/-- **The merge's accepting step makes `hasRow` at the head, from the closed test.** -/
theorem merge_makes_row_of_all (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (lin : Params.LinShape)
    (hB : pendAllB P.lay lin = true) (he : ∃ c, EntryAt s' c) :
    Johnson.Desc.First.Walk.Law.hasRow P.lay 1 lin s' = true :=
  merge_makes_row P h lin (pend_of_all P lin (pendAll_says hB) h) he

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.unit_of_shape
#print axioms VerifiableInference.Desc.First.MergeLaw.pend_of_all
#print axioms VerifiableInference.Desc.First.MergeLaw.pendAll_says
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_makes_row_of_all
