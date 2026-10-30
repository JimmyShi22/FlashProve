-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/KeyBack/FreeOfSub.lean: the four fields of what the planner returns that do not hang
on the digest are the written full-size value, where two routines of the planner return the written
values at the run's sub-proofs.

THESE LAWS MOVE A DEBT ONE STEP DOWN; THEY PAY NONE OF IT. Each takes two returns as premises: that
the sizing of a proof file returns the written sizes (s₁), and that the routine for its first chain
returns the first written plan (s₂), both at the field `sub` of the run's shapes. THE PREMISES ARE
NOT SHOWN TOGETHER IN THIS FILE; where they are used together, and how far: R7AtMade.lean's head.

What it is for. The row on the lengths of the seven strings of parameter bytes
(Johnson/AtFull/KeyBack/BytesShort.lean) takes the equation `freeOf made = writtenMade`. The law
`free_of_sized` (Johnson/Goal/Written/ChainsW.lean) has it from the sizes and the first plan of what
the planner returns. Both hang on `x.sub` alone: the sizes of a proof file by `sized_proof`
(OnBytes/Plan/PlanListsProof.lean), the first plan by the last clause of `sixOfSized`
(Johnson/Goal/Written/MadeOfSized.lean).

`free_of_sub`: at what `configure` returns at the written lines, where the key's sizing returns the
written sizes. `free_at_made`: in the goals' scope, at what `Key.madeAt` returns. Its first lines
are those of `four_at_scope` (BytesShort.lean).

In `free_at_made` the letters lay and lf are free, as in `four_at_scope`. The use is at lay := Z.lay
and lf := some Z.lay; at another lay the premise S may be one that cannot be met.

Limits. The full size alone. Nothing on soundness.
-/
import Johnson.AtFull.KeyBack.BytesShort
import Johnson.Goal.Written.ChainsW
import Johnson.Goal.Numbers.MadeInScope
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params OnBytes.Model.Verify
open Johnson.G (layoutFull)
open Johnson.G.MadeFree
open VerifiableInference.PlanWritten (proofSizedFull publicOfO publicSteps_of_O)
open VerifiableInference.PlanWritten.Joined (writtenMade free_of_sized sized_of_configure
  sixOfSized)
open VerifiableInference.Number.ByRuns
open Lk6.AtPlan

/-- Where the sizing of a proof file and the routine for its first chain return the written values
at `x.sub`, the four fields of what `configure` returns are the written value. -/
theorem free_of_sub {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hg : configure recordLines x cfg bits = .ok made)
    (hk : Plan.keySized recordLines x.ranges = some keyFull)
    (s₁ : proofSized recordLines x.sub = some proofSizedFull)
    (s₂ : firstPlan proofSizedFull x.sub = .ok proofThree.A.plan) :
    freeOf made = writtenMade := by
  have hz := (OnBytes.Params.configure_plans hg).1
  have hp : made.sized.proof = proofSizedFull :=
    Option.some.inj ((OnBytes.Params.sized_proof hz).symm.trans s₁)
  have hs := sized_of_configure hg hk hp
  obtain ⟨_, _, F, hF, hf⟩ := sixOfSized recordLines x cfg bits made hg hs
  have eF : F = proofThree.A.plan := Except.ok.inj (hf.symm.trans s₂)
  refine free_of_sized hg hs ?_
  rw [hF, eF]
  rfl

/-- The same in the goals' scope, at what `Key.madeAt` returns. -/
theorem free_at_made {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {lf : Option ByteArray} {X₀ : Public} (hX : publicOfO o Z.pol Z.KL lf = .ok X₀)
    {lay cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : VerifiableInference.Desc.Key.madeAt X₀ lay cfg = .ok m)
    (S : ∀ links shapes, shapesOf X₀ (some lay) = .ok (links, shapes) →
      proofSized recordLines shapes.sub = some proofSizedFull ∧
        firstPlan proofSizedFull shapes.sub = .ok proofThree.A.plan) :
    freeOf m.p.chains.made = writtenMade := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hX
  obtain ⟨hf, hw⟩ := args_of_steps (publicSteps_of_O hX)
  obtain ⟨links, shapes, hs, hg, -⟩ :=
    Fo.chainsOf_cut (VerifiableInference.Desc.Key.madeAt_chains hm)
  rw [hf] at hg
  obtain ⟨s₁, s₂⟩ := S links shapes hs
  exact free_of_sub hg (keySized_returns hw (shapesOf_ranges hs)) s₁ s₂

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.free_of_sub
#print axioms Johnson.AtFull.KeyBack.free_at_made
