-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SLot.lean: the proofs of `HeadMergeSLotIs` and
`HeadMergeGoodSeated` (Honest/K11/Plays/SLotStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The lot of halves: by definition: the row is two parts beside two simulators. The side: where
`Side.seated` answers, its sub-protocol is the first member at the place and its row is the row:
then `headMergeGoodAll` (GoodAll.lean of this folder).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.SLotStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.GoodAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11

/-- **The lot of halves is the kind's.** -/
theorem headMergeSLotIs : HeadMergeSLotIs := fun _ _ _ _ _ _ => rfl

/-- **`Good` at the side that is taken off a list.** -/
theorem headMergeGoodSeated : HeadMergeGoodSeated := by
  intro W₀ Rc Xi Tr X bs fs₀ σ₀ φ Bk ord chain firstTree pre P claims weights name hσ hmem hown
  have hσ' : ((bs.find? fun b => b.place == headMergePlace P).map fun b =>
      ({ block := b, row := headMergeSided P claims weights
         fall := fallOf fs₀ (headMergePlace P) } :
        Side _ _ (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)) = some σ₀ := hσ
  rw [hmem] at hσ'
  obtain rfl := Option.some.inj hσ'
  exact headMergeGoodAll W₀ Rc Xi Tr X _ φ Bk ord chain firstTree pre P claims weights name rfl rfl
    hown

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.headMergeSLotIs
#print axioms ProofFile.Honest.K11.headMergeGoodSeated
