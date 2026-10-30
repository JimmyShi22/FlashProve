-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/KeyBack/TwoShort.lean: the parameter bytes of a proof file's shared chain and of its
second chain have fewer than 2 ^ 24 bytes each, where the sizing of a proof file returns the written
sizes at the run's sub-proofs. With `four_at_scope` (Johnson/AtFull/KeyBack/BytesShort.lean) that
makes six of the seven strings.

THESE LAWS MOVE A DEBT ONE STEP DOWN; THEY PAY NONE OF IT. That the sizing returns the written sizes
(s₁) is a premise. IT IS NOT SHOWN IN THIS FILE; how far it is used: the head of R7AtMade.lean.

Why these two ask less than the first chain's string. The planner spells into them their own plans,
the codes and the shape of the test on the table (`configure_bytes`,
OnBytes/Model/ReadBackMade.lean). The two plans follow from the sizes (`sixOfSized`,
Johnson/Goal/Written/MadeOfSized.lean). Neither the first plan, nor the layout, nor the links'
identifiers stand in them.

`two_short`: at what `configure` returns at the written lines. It goes as `four_short`
(BytesShort.lean) goes. `two_at_scope`: in the goals' scope, at what `Key.madeAt` returns.

In `two_at_scope` the letters lay and lf are free, as in `four_at_scope`. The use is at lay := Z.lay
and lf := some Z.lay.

Limits. The full size alone. The bounds are not sharp. The digest's 32 bytes are a premise.
Nothing on soundness.
-/
import Johnson.AtFull.KeyBack.BytesShort
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

/-- The two strings, at what `configure` returns at the written lines. -/
theorem two_short {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hg : configure recordLines x cfg bits = .ok made)
    (hk : Plan.keySized recordLines x.ranges = some keyFull)
    (s₁ : proofSized recordLines x.sub = some proofSizedFull) (h32 : cfg.size = 32) :
    made.shared.size < 2 ^ 24 ∧ made.second.size < 2 ^ 24 := by
  have hz := (OnBytes.Params.configure_plans hg).1
  have hp : made.sized.proof = proofSizedFull :=
    Option.some.inj ((OnBytes.Params.sized_proof hz).symm.trans s₁)
  have hs := sized_of_configure hg hk hp
  obtain ⟨_, _, F, hF, _⟩ := sixOfSized recordLines x cfg bits made hg hs
  obtain ⟨_, _, _, F', S2, S3, _, ep, _, _, _, _, _, e6, e7⟩ := configure_bytes hg
  rw [hF] at ep
  obtain ⟨-, rfl, rfl⟩ : F = F' ∧ proofThree.B.plan = S2 ∧ proofThree.C.plan = S3 := by
    simpa using ep
  have i0 : _root_.AtFull.KeyBack.itemsSize [] < 2 ^ 22 := by decide
  rw [e6, e7, hp]
  exact ⟨_root_.AtFull.KeyBack.size_params_lt _root_.AtFull.KeyBack.few_proof2 h32
      (Nat.lt_trans _root_.AtFull.KeyBack.proofLin_items (by decide)),
    _root_.AtFull.KeyBack.size_params_lt _root_.AtFull.KeyBack.few_proof3 h32 i0⟩

/-- The same in the goals' scope, at what `Key.madeAt` returns. -/
theorem two_at_scope {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {lf : Option ByteArray} {X₀ : Public} (hX : publicOfO o Z.pol Z.KL lf = .ok X₀)
    {lay cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : VerifiableInference.Desc.Key.madeAt X₀ lay cfg = .ok m) (h32 : cfg.size = 32)
    (S₁ : ∀ links shapes, shapesOf X₀ (some lay) = .ok (links, shapes) →
      proofSized recordLines shapes.sub = some proofSizedFull) :
    (m.p.chains.bytes .proofShared).size < 2 ^ 24 ∧
      (m.p.chains.bytes .proofSecond).size < 2 ^ 24 := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hX
  obtain ⟨hf, hw⟩ := args_of_steps (publicSteps_of_O hX)
  obtain ⟨links, shapes, hs, hg, -⟩ :=
    Fo.chainsOf_cut (VerifiableInference.Desc.Key.madeAt_chains hm)
  rw [hf] at hg
  exact two_short hg (keySized_returns hw (shapesOf_ranges hs)) (S₁ links shapes hs) h32

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.two_short
#print axioms Johnson.AtFull.KeyBack.two_at_scope
