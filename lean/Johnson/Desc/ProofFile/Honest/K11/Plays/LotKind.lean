-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LotKind.lean: the proofs of `HeadMergeLotKind` and
`HeadMergeLotFind` (Honest/K11/Plays/LotKindStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The lot's list has one half, at `headMergePlace` of the lot's numbers, whose kind is K11 by its
text. Under the head that place is `IM.k11Place`: its link's number is 24 (`headMergeAtFull`,
Johnson/Desc/K11/Exchange/AtFull.lean), its piece 9 by the lot's text.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotKindStatement
import Johnson.Desc.K11.Exchange.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)

/-- **Every half of the kind's lot stands at a place of the kind K11.** -/
theorem headMergeLot_kind : HeadMergeLotKind := by
  intro W₀ Rc Tr X claims weights Z G x hx
  obtain rfl : x = headMergeHalf (claims Z G) weights (_root_.K11.parOf Z G) :=
    List.mem_singleton.1 hx
  rfl

/-- **In the lot's own list the search by the merge's address finds the kind's half.** -/
theorem headMergeLot_find : HeadMergeLotFind := by
  intro Z D r Zp Np cF x h W₀ Rc Tr X Bs claims weights hmade
  obtain ⟨Bs', _, _, hmade', _, _, _, _, _, hlink⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hmade'.symm.trans hmade)
  have hp : headMergePlace (_root_.K11.parOf Zp Bs'.G₀) = IM.k11Place := by
    show (⟨1, some (_root_.K11.parOf Zp Bs'.G₀).link, 9, .K11⟩ : VerifiableInference.Desc.Place) = _
    rw [hlink]
  show List.find? _ [headMergeHalf (claims Zp Bs'.G₀) weights (_root_.K11.parOf Zp Bs'.G₀)] = _
  rw [List.find?_cons_of_pos (by
    show (headMergePlace (_root_.K11.parOf Zp Bs'.G₀) == IM.k11Place) = true
    rw [hp]
    exact beq_self_eq_true _)]

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.headMergeLot_kind
#print axioms ProofFile.Honest.K11.headMergeLot_find
