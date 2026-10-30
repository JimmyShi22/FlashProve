-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/RidesWhole.lean: the proofs of the two statements of
Honest/K11/Plays/RidesWholeStatement.lean, to the letter. Lemmas; none of the library's goals.

How. The first: a closed fact on the library's written lists, by evaluation in Lean's kernel
(`decide +kernel`, under a raised `maxRecDepth`). The second: the frame's authors'
`ridesPastS_shares` (Honest/Thread/SharesS.lean): the debt is its shares at the items that are open
at the border and that the row neither shuts nor owes; by the first each such item is one of the
seventeen; then case by case: their `k11_rides_pins`, `k11RowsRide`, `sixFormsRide_at_head`, and the
three premises. The kind's clause is the first half of `K11KeepsYes`.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.RidesWholeStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.SixRide
import Johnson.Desc.ProofFile.Honest.K11.Plays.RowRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.First (Item)
open ProofFile.Honest.FirstThread

set_option maxRecDepth 1000000 in
/-- **The items that are open across 346.** -/
theorem across_at_346 : AcrossAt346 := by
  unfold AcrossAt346
  decide +kernel

/-- **The debt at the head, from three shares.** -/
theorem ridesPastS_at_head : RidesPastSAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs hB hk hP
    hW1 hW2
  have hk' : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s
      s' → Johnson.Desc.First.ForkMerge.Returns.K11Keeps (_root_.K11.parOf Zp Bs.G₀) s s' :=
    fun s s' hK => (hk s s' hK).1
  obtain ⟨q1, _, q3⟩ := k11_rides_pins h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (_root_.K11.parOf Zp Bs.G₀) hk'
  have qr := k11RowsRide Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd
    Kp w (_root_.K11.parOf Zp Bs.G₀) hk'
  have qf := sixFormsRide_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂
    b₀ Vd Rd Kp w Bs hB hk
  refine ridesPastS_shares _ SaidOk fun i hi h1 h2 => ?_
  have hm := across_at_346 i hi h1 h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact ridesPastAtS_of _ SaidOk q3
  · exact ridesPastAtS_of _ SaidOk (q1 24 1)
  · exact ridesPastAtS_of _ SaidOk (q1 24 2)
  · exact ridesPastAtS_of _ SaidOk (qr 24 .carried)
  · exact ridesPastAtS_of _ SaidOk (qr 24 (.sample 0))
  · exact ridesPastAtS_of _ SaidOk (qr 24 (.sample 1))
  · exact ridesPastAtS_of _ SaidOk (qr 24 (.sample 2))
  · exact ridesPastAtS_of _ SaidOk (qr 24 .position)
  · exact qf (3, "objects") (by decide)
  · exact qf (3, "planes") (by decide)
  · exact qf (4, "join") (by decide)
  · exact qf (4, "own") (by decide)
  · exact qf (6, "small") (by decide)
  · exact qf (8, "objects") (by decide)
  · exact hP
  · exact hW1
  · exact hW2

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.across_at_346
#print axioms ProofFile.Honest.K11.ridesPastS_at_head
