-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/KeyBackOfShapes.lean: The key file's back returns, in the goals' scope,
from the two makers' returns and three equations on the shapes that `shapesOf` returns. Two calls
each. Nothing is evaluated here.

KeyBackAtFixed.lean has the return from one named premise h7: the proof file's three strings of
parameter bytes are shorter than 2 ^ 64. R7AtMade.lean has all seven strings' bound from three
equations. Here the two are joined, in both forms in which R7AtMade.lean takes the equations.

  `keyBack_at_fixed_of_debts`: the equations at whatever `shapesOf` returns (over `r7_at_made`).
  `keyBack_at_fixed_of_shapes`: at one named return of `shapesOf` (over `r7_of_shapes`): the form
    for whoever holds that return.
The three equations. The proof file's sizes, made from the shapes' sub-proofs, are the written
ones. Its first plan, made from the same, is the written one. The shapes' layout is the written
one. They are premises and are paid here by nothing: this file moves h7's debt one step down.
Two of them are returns (of `proofSized`, a `some`; of `firstPlan`, an `.ok`). That they hold at
every file in the scope is shown nowhere.
It takes returns and gives one, as KeyBackAtFixed.lean does: hX and hm are the returns of
`publicOfO` and of `Key.madeAt`; that either returns at any files is not shown here. That the
premises can be met together is not shown in this file: if they could not, the two statements would
be idle and nothing here would show it. In other files the premises of `keyBack_at_fixed_of_shapes`
are used together inside the proof of `AtFullSide.Planner.theKeyLaid_zFull_returns`
(AtFullSide/Planner/KeyLaidReturns.lean), in a side library outside the main library (one theorem
beneath `theKeyLaid_zFull_returns`, `Johnson.Unfolds.Layout.lay_chars` in
AtFullSide/Layout/TieRfl.lean, passes Lean's kernel only at a thread stack larger than the default;
Lean's re-checker leanchecker, run on it, fails at each shell stack limit that was tried, up to 1
GiB; no independent checker has given a verdict on it), and in that proof only at Lean's written
copy of the full-size public files (`VerifierAndGoals.storedPublicFiles`: three terms written in Lean, tied to the
repository's files by no theorem; the example's weights are synthetic), at the second hash
function (`OnBytes.secondHashFunction`) and the constant digest `Key.fixedDigest` (32 bytes of 1), at which the
key file's piece is laid for the verifier's text, where no digest is handed in; not the files' own.
That proof calls `Johnson.AtFull.Top.theKeyLaid_zFull` (Johnson/AtFull/Top/KeyLaidZFull.lean: that
theorem takes two facts on that copy's layout file as premises, which the side library shows), whose
proof calls `keyBack_at_fixed_of_shapes`. No theorem is known that states the conjunction by
itself, nor any proof that calls `keyBack_at_fixed_of_debts`. Its premise S follows from
the premises hs, s₁, s₂ and s₃ of `keyBack_at_fixed_of_shapes`: that step stands inside the proof of
`r7_of_shapes` (R7AtMade.lean), which `keyBack_at_fixed_of_shapes` calls. `theKeyLaid_zFull_returns`
speaks of `VerifierAndGoals.storedPublicFiles` alone, not of other files in scope.
Limits. As in KeyBackAtFixed.lean. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.KeyBackAtFixed
import Johnson.AtFull.KeyBack.R7AtMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open VerifiableInference VerifiableInference.Desc
open Johnson.G.OfPlan (Made)
open OnBytes OnBytes.Params OnBytes.Model.Verify
open OnBytes.Model.Stages (LinkH)
open Johnson.G (layoutFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns
open Lk6.AtPlan

variable {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray} {X₀ : Public} {m : Made}

/-- The return, from the three equations at whatever `shapesOf` returns. -/
theorem keyBack_at_fixed_of_debts (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m)
    (S : ∀ links shapes, shapesOf X₀ (some Z.lay) = .ok (links, shapes) →
      proofSized recordLines shapes.sub = some proofSizedFull ∧
        firstPlan proofSizedFull shapes.sub = .ok proofThree.A.plan ∧
        shapes.layout = layoutFull) :
    Key.keyDataAndDecisionOfPlannerAnswer X₀ Z.lay m = .ok (Johnson.G.writtenKFull,
                             ((Key.descriptionFromSource (sourceKFull m) Johnson.KB8.rangesNumsFull
                               Johnson.KB8.laterPlacesFull).pull Key.keyInstanceOfOutOfDomainSample).run) :=
  have h := r7_at_made hZ hX hm Key.fixedDigest_size S
  keyBack_at_fixed_of_rest hZ hX hm ⟨h .proofFirst, h .proofShared, h .proofSecond⟩

/-- The return, from the three equations at one named return of `shapesOf`. -/
theorem keyBack_at_fixed_of_shapes (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m)
    {links : Array LinkH} {shapes : Shapes}
    (hs : shapesOf X₀ (some Z.lay) = .ok (links, shapes))
    (s₁ : proofSized recordLines shapes.sub = some proofSizedFull)
    (s₂ : firstPlan proofSizedFull shapes.sub = .ok proofThree.A.plan)
    (s₃ : shapes.layout = layoutFull) :
    Key.keyDataAndDecisionOfPlannerAnswer X₀ Z.lay m = .ok (Johnson.G.writtenKFull,
                             ((Key.descriptionFromSource (sourceKFull m) Johnson.KB8.rangesNumsFull
                               Johnson.KB8.laterPlacesFull).pull Key.keyInstanceOfOutOfDomainSample).run) :=
  have h := r7_of_shapes hZ hX hm Key.fixedDigest_size hs s₁ s₂ s₃
  keyBack_at_fixed_of_rest hZ hX hm ⟨h .proofFirst, h .proofShared, h .proofSecond⟩

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.keyBack_at_fixed_of_debts
#print axioms Johnson.AtFull.KeyBack.keyBack_at_fixed_of_shapes
