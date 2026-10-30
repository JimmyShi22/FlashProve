-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/KeyBack/R7AtMade.lean: each of the seven strings of parameter bytes in what
`Key.madeAt` returns has fewer than 2 ^ 64 bytes, in the goals' scope, where three things hold of
the run's shapes.

These laws move a debt one step down; they pay none of it. The three things are premises: that the
sizing of a proof file returns the written sizes at the shapes' field `sub` (s₁); that the routine
for its first chain returns the first written plan there (s₂); that the shapes' layout is the
written one (s₃). That the premises can be met together is not shown in this file. In other files
they are used together inside the proof of `AtFullSide.Planner.theKeyLaid_zFull_returns`
(AtFullSide/Planner/KeyLaidReturns.lean), in a side library outside the main library (one theorem
beneath `theKeyLaid_zFull_returns`, `Johnson.Unfolds.Layout.lay_chars` in
AtFullSide/Layout/TieRfl.lean, passes Lean's kernel only at a thread stack larger than the default;
Lean's re-checker leanchecker, run on it, fails at each shell stack limit that was tried, up to 1
GiB; no independent checker has given a verdict on it), and in that proof only at Lean's written
copy of the full-size public files (`VerifierAndGoals.storedPublicFiles`: three terms written in Lean, tied to the
repository's files by no theorem; the example's weights are synthetic), at the second hash
function (`OnBytes.secondHashFunction`) and the constant digest `Key.fixedDigest` (32 bytes of 1), at which the
key file's piece is laid for the verifier's text, where no digest is handed in; not the files' own.
That proof reaches `r7_of_shapes`, which calls `r7_at_made`, through
`Johnson.AtFull.Top.theKeyLaid_zFull` (Johnson/AtFull/Top/KeyLaidZFull.lean: that theorem takes two
facts on that copy's layout file as premises, which the side library shows) and
`keyBack_at_fixed_of_shapes` (Johnson/AtFull/KeyBack/KeyBackOfShapes.lean). No theorem is known
that states the conjunction by itself. `theKeyLaid_zFull_returns` speaks of
`VerifierAndGoals.storedPublicFiles` alone, not of other files in scope.

`r7_at_made`: the three as one premise on whatever `shapesOf` returns: the form of the premise on
the layout in `r7_of_layout` (Johnson/AtFull/KeyBack/BytesShort.lean), which it calls, with
`free_at_made` (Johnson/AtFull/KeyBack/FreeOfSub.lean). `r7_of_shapes`: the same for whoever holds
one return of `shapesOf` and the three things at it.

The letters lay and lf are free, as in `four_at_scope` (BytesShort.lean). The use is at lay := Z.lay
and lf := some Z.lay; at another lay the premises may be ones that cannot be met.

Limits. The full size alone. The digest's 32 bytes are a premise. Nothing on soundness.

-/
import Johnson.AtFull.KeyBack.FreeOfSub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params OnBytes.Model.Verify
open OnBytes.Model.Stages (LinkH)
open Johnson.G (layoutFull)
open Johnson.G.MadeFree
open VerifiableInference.PlanWritten (proofSizedFull publicOfO publicSteps_of_O)
open VerifiableInference.PlanWritten.Joined (writtenMade free_of_sized sized_of_configure
  sixOfSized)
open VerifiableInference.Number.ByRuns
open Lk6.AtPlan

/-- **All seven strings**, from the three things at whatever `shapesOf` returns. -/
theorem r7_at_made {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {lf : Option ByteArray} {X₀ : Public} (hX : publicOfO o Z.pol Z.KL lf = .ok X₀)
    {lay cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : VerifiableInference.Desc.Key.madeAt X₀ lay cfg = .ok m) (h32 : cfg.size = 32)
    (S : ∀ links shapes, shapesOf X₀ (some lay) = .ok (links, shapes) →
      proofSized recordLines shapes.sub = some proofSizedFull ∧
        firstPlan proofSizedFull shapes.sub = .ok proofThree.A.plan ∧
        shapes.layout = layoutFull) :
    ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64 :=
  _root_.AtFull.KeyBack.r7_of_layout hm h32
    (free_at_made hZ hX hm fun links shapes hs => ⟨(S links shapes hs).1, (S links shapes hs).2.1⟩)
    fun links shapes hs => (S links shapes hs).2.2

/-- The same from one return of `shapesOf` and the three things at it. -/
theorem r7_of_shapes {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {lf : Option ByteArray} {X₀ : Public} (hX : publicOfO o Z.pol Z.KL lf = .ok X₀)
    {lay cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : VerifiableInference.Desc.Key.madeAt X₀ lay cfg = .ok m) (h32 : cfg.size = 32)
    {links : Array LinkH} {shapes : Shapes} (hs : shapesOf X₀ (some lay) = .ok (links, shapes))
    (s₁ : proofSized recordLines shapes.sub = some proofSizedFull)
    (s₂ : firstPlan proofSizedFull shapes.sub = .ok proofThree.A.plan)
    (s₃ : shapes.layout = layoutFull) :
    ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64 :=
  r7_at_made hZ hX hm h32 fun links' shapes' hs' => by
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj (hs.symm.trans hs'))
    exact ⟨s₁, s₂, s₃⟩

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.r7_at_made
#print axioms Johnson.AtFull.KeyBack.r7_of_shapes
