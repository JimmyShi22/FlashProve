-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/LkAtFull.lean: the proof of `LkAtFull`
(Johnson/Desc/K11/Exchange/LkAtFullStatement.lean), to the letter. A lemma; none of the library's
goals.

How: two calls. In the goals' scope the public data's layout has these two numbers (`m0lk_in_scope`,
Johnson/Desc/Sound/K11Tests/NumsHeadInScope.lean); the kind's layout is the public data's
(`hlay_at`, Johnson/Top/H0/MergeLaw/PlanNumsAt.lean).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.LkAtFullStatement
import Johnson.Desc.Sound.K11Tests.NumsHeadInScope
import Johnson.Top.H0.MergeLaw.PlanNumsAt
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc.First.MergeLaw (hlay_at)

/-- **The layout's two numbers, and the count of slots.** -/
theorem lkAtFull : LkAtFull := by
  intro Z D r Zp Np cF x h Bs hmade
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := (IM.base_made hmade).2.2.1
  obtain ⟨e1, e2⟩ := LT28.K11Tests.m0lk_in_scope h.scope h.pubOne
  have e := hlay_at hG
  have l1 : (K11.parOf Zp Bs.G₀).lay.lk = 18 := by
    rw [← e]
    exact e2
  have l2 : (K11.parOf Zp Bs.G₀).lay.m0 = 3076096 := by
    rw [← e]
    exact e1
  exact ⟨l1, l2, by rw [l1]⟩

end Johnson.Desc.First.ForkMerge.Exchange

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.lkAtFull
