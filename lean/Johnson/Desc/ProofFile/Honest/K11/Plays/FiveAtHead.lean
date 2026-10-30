-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FiveAtHead.lean: the proof of `FiveAtHead`
(Honest/K11/Plays/FiveAtHeadStatement.lean), to the letter. A lemma; none of the library's goals.

How: five calls: `plays_at_head` (PlaysAtHead.lean), `acceptedS_at_head` (AcceptedAtHead.lean),
`behindYesS_at_head_of_Rd` (BehindYesAtHead.lean), `exchangeS_at_head` (ExchangeWhole.lean: it takes
the third call's end) and `ridesPastS_at_head` (RidesWhole.lean), all of this folder. The thread's
list of halves is the prover's first list by the text of `lettersHead`. The kind's clause is the
first half of `K11KeepsYes`.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.FiveAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.ExchangeWhole
import Johnson.Desc.ProofFile.Honest.K11.Plays.RidesWhole
import Johnson.Desc.ProofFile.Honest.K11.Plays.BehindYesAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.PlaysAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11

/-- **All five debts at 346, at the head's thread.** -/
theorem five_at_head : FiveAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs weights
    c₀ hB hb hhalf hM hC hk hk' hRd hP hW1 hW2
  have hBe := behindYesS_at_head_of_Rd Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item
    n₁ n₂ b₀ Vd Rd Kp w Bs hB hb hk' hRd
  exact ⟨(plays_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd
      Kp w Bs _ weights hB hhalf).2 SaidOk,
    acceptedS_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp
      w Bs _ weights hB hhalf,
    hBe,
    exchangeS_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp
      w Bs weights c₀ hB hb hhalf hM hC (fun s s' hK => (hk s s' hK).1) hBe,
    ridesPastS_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp
      w Bs hB hk hP hW1 hW2⟩

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.five_at_head
