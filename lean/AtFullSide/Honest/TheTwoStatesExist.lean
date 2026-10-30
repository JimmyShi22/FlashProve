-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheTwoStatesExist.lean: the two types of states at which TheLettersLast.lean and
TheOneObject.lean ask an Inhabited instance have a member: under a head at a return, the online
description's first states of the first and the shared chain, at one written instance.

  `the_two_states_exist`          under a head
  `the_two_states_exist_stored`   with no premise: at the stored full-size files there is a head

Limits. Existence alone: no instance is declared, and which member a default should be is not said.

No property is claimed.
-/
import AtFullSide.Honest.TheCapstoneFromTheObject

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest (OnlineProverWithDescription IndexCommitterCoins Cells)
open ProofFile.Honest.FirstThread (HeadAtReturn)

/-- **Both types of states have a member, under a head.** -/
theorem the_two_states_exist {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (h : HeadAtReturn Z A) : Nonempty P5J.TS ∧ Nonempty Desc.K14.St :=
  ⟨⟨h.description.start₁ (h.description.pub
      (LPFD.Full.instanceAsPlainRecord (FlashProve.dataAtFiles FlashProve.flashProveData Z).G.z₀))⟩,
    ⟨h.description.start₂ (h.description.pub
      (LPFD.Full.instanceAsPlainRecord (FlashProve.dataAtFiles FlashProve.flashProveData Z).G.z₀))⟩⟩

/-- **Both have a member.** -/
theorem the_two_states_exist_stored : Nonempty P5J.TS ∧ Nonempty Desc.K14.St := by
  have named : VerifierAndGoals.NamedFiles VerifierAndGoals.storedPublicFiles := Or.inl rfl
  obtain ⟨A, made⟩ := ProofFile.Honest.K1.baseMaker_returns VerifierAndGoals.storedPublicFiles
    (AtPublicFiles.AtFiles.HonestTerm.scope_named named) (AtPublicFiles.AtFiles.HonestTerm.live_named named)
  obtain ⟨h, -⟩ := ProofFile.Honest.K1.headAtReturn_baseMaker VerifierAndGoals.storedPublicFiles
    (AtPublicFiles.AtFiles.HonestTerm.scope_named named) (AtPublicFiles.AtFiles.HonestTerm.live_named named) made
  exact the_two_states_exist h

end AtFullSide.Honest

#print axioms AtFullSide.Honest.the_two_states_exist
#print axioms AtFullSide.Honest.the_two_states_exist_stored
