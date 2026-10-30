-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/AtFull.lean: the proofs of `StepFoundInScope` and `HeadMergeAtFull`
(Johnson/Desc/K11/Exchange/AtFullStatement.lean), to the letter. Lemmas; none of the library's
goals.

How. The step is found: the head's link's hearing block number 8 is the lot's block, alone
(`IM.k11_of`, Johnson/IMR/K11Seat.lean); where the description passes its tests on the plan, a lot's
block that stands alone passes its own (`IM.plan_alone`, Johnson/IMR/PlanAt.lean); the lot's block's
own test holds "the step is found" as its second clause (`K11.blkAt`,
Johnson/Desc/ProofFile/Lot/K11.lean). Under the head: it holds an opening of the description's
return at its own letters, that the public files are in scope, what is read off them, and that the
description passes its tests on the plan (its fields laid, scope, reads). Then `headMergeInScope`
(InScope.lean of this folder). The data's links are, by definition, the reader of a link off the
public part alone; their list of segments is the library's list at the full size; their layout is
the public part's, which is the ground's (`IM.blank_ground`, Johnson/IMR/PureJoin.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.AtFullStatement
import Johnson.Desc.K11.Exchange.InScope
import Johnson.IMR.PlanAt
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange

/-- **The step's name is found.** -/
theorem stepFoundInScope : StepFoundInScope := by
  intro P pp lay F Z Bs base c A B hS hR O hp
  obtain ⟨Lk, b, e1, e2, hla, _⟩ := IM.k11_of hS hR O
  have h0 : (K11.blkAt Z "H.8.call" Bs.G₀).planOk = true := IM.plan_alone O hp e1 e2 hla
  have h1 : ((K11.blk (K11.parAt Z "H.8.call" Bs.G₀)).planOk &&
      (K11.sentAt? Z "H.8.call").isSome) = true := h0
  exact (Bool.and_eq_true _ _ ▸ h1).2

/-- **The kind's block under the one head.** -/
theorem headMergeAtFull : HeadMergeAtFull := by
  intro Z D r Zp Np cF x h
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hfound := stepFoundInScope _ _ _ _ _ _ _ _ _ _ h.scope h.reads O h.laid.planOk
  obtain ⟨Lk, name, _, e2, e3, e4, e5⟩ :=
    headMergeInScope _ _ _ _ _ _ _ _ _ _ h.scope h.reads O hfound
  obtain ⟨_, _, eW, _, _⟩ := IM.blank_ground O.blank
  refine ⟨Bs, Lk, name, O.made, e2, rfl, ?_, e3, e4, e5⟩
  show Zp.p.X.layers.wsLay = Bs.G₀.W.layers.wsLay
  rw [eW]

end Johnson.Desc.First.ForkMerge.Exchange

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.stepFoundInScope
#print axioms Johnson.Desc.First.ForkMerge.Exchange.headMergeAtFull
