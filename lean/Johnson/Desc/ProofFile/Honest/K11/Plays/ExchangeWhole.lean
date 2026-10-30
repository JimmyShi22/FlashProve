-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/ExchangeWhole.lean: the proofs of the four statements of
Honest/K11/Plays/ExchangeWholeStatement.lean, to the letter. Lemmas; none of the library's goals.

How. The first two: closed facts on the library's written lists, by evaluation in Lean's kernel
(`decide +kernel`, under a raised `maxRecDepth`). The third: the frame's authors' `exchangeS_iff`
(Honest/Thread/SharesS.lean): the debt is its shares at the items that the row owes; the thread's
row is the written one by the text of `lettersHead`; by the first each such item is one of the five.
The fourth: the kind's two items by `exchange_at_head` (SeatedAtHead.lean of this folder); the two
pins by the frame's authors' `k11_pins_again`, with the second; pinW's share by their
`exchangeAt_pinW` and `exchangeAtS_of`.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ExchangeWholeStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatedAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.First (Item)
open ProofFile.Honest.FirstThread

set_option maxRecDepth 1000000 in
/-- **What the forward row number 346 owes.** -/
theorem owes_at_346 : OwesAt346 := by
  unfold OwesAt346
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The two pins are open at 346.** -/
theorem pinsOpen_at_346 : PinsOpenAt346 := by
  unfold PinsOpenAt346
  decide +kernel

/-- **The debt from its five shares.** -/
theorem exchangeS_of_five : ExchangeSOfFive := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said h1 h2
    h3 h4 h5
  refine (exchangeS_iff _ Said).2 fun i hi => ?_
  have hm := owes_at_346 i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- **The debt at the head.** -/
theorem exchangeS_at_head : ExchangeSAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs weights
    c₀ hB hb hhalf hM hC hk hBe
  obtain ⟨e1, e2⟩ := exchange_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁
    n₂ b₀ Vd Rd Kp w Bs weights c₀ hB hb hhalf hM hC
  obtain ⟨p1, p2⟩ := k11_pins_again h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (_root_.K11.parOf Zp Bs.G₀) hk SaidOk hBe
  exact exchangeS_of_five Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd
    Kp w SaidOk e1 e2
    (exchangeAtS_of _ SaidOk (exchangeAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w 346))
    (p1 24 0 pinsOpen_at_346.1) (p2 pinsOpen_at_346.2)

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.owes_at_346
#print axioms ProofFile.Honest.K11.pinsOpen_at_346
#print axioms ProofFile.Honest.K11.exchangeS_of_five
#print axioms ProofFile.Honest.K11.exchangeS_at_head
