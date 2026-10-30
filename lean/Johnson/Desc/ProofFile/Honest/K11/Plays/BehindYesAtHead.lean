-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/BehindYesAtHead.lean: the proofs of `BehindYesSAtHead` and
`BehindYesSAtHeadOfRd` (Honest/K11/Plays/BehindYesAtHeadStatement.lean), to the letter. Lemmas; none
of the library's goals.

How. `behindYesS_at_head`: `headMergeBehindYesS` (FormsRide.lean of this folder) at the merge.
`behindYesS_at_head_of_Rd`: by the first, with the stronger clause opened.
The merge writes neither the reply nor the prover's input: so the reply rides from 346 to 347.
The thread's form behind the step is the frame's authors'
`k11_form_behind` (Honest/Thread/K11FormBehind.lean), which takes no clause of keeps.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.BehindYesAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.FormsRide
import Johnson.Desc.ProofFile.Honest.Thread.K11FormBehind
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.K11.Exchange.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open ProofFile.Honest.FirstThread (lettersHead k11_form_behind)

/-- **The frame's debt BehindS at the merge's member, at the head's thread, at the stronger clause,
from two premises on the thread's free letters.** -/
theorem behindYesS_at_head : BehindYesSAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs hmade
    hkeeps hrides
  obtain ⟨Bs', _, name, hmade', _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hmade'.symm.trans hmade)
  exact headMergeBehindYesS Bk _ _ X _
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk 346
    (_root_.K11.parOf Zp Bs'.G₀) name IM.k11Place hfl hkeeps
    (fun blk k s m E ds y cols s' hT hS hblk _ =>
      (k11_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hT hS).1)
    (fun blk k s m E ds y cols s' hT hS hblk _ =>
      (k11_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hT hS).2)
    (fun blk k s m E ds y cols s' hT hS hblk hK => hrides blk k s m E ds y cols s' hT hS hblk hK)

/-- **The same, with the rider on the reply paid.** -/
theorem behindYesS_at_head_of_Rd : BehindYesSAtHeadOfRd := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs hmade hb₀
    hkeeps hRd
  refine behindYesS_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd
    Rd Kp w Bs hmade hkeeps fun blk k s m E ds y cols s' hT hS hblk hK =>
      ⟨fun _ => ?_, hRd blk k s m E ds y cols s' hT hS hblk hK⟩
  have hT' := hT.1
  unfold Thr at hT'
  obtain ⟨-, -, -, -, -, hr, -⟩ := hT'
  have h1 : s.out.reply = some m.st.input.x.asked := hr.1 hb₀
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  have h2 : y.2.st.input = m.st.input := (play_mid l ds [] m y hy).1
  obtain ⟨⟨⟨a, wo, v, β, -, -, -, -, -, -, rfl⟩, -⟩, -⟩ := hK
  rw [h2]
  exact h1

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.behindYesS_at_head
#print axioms ProofFile.Honest.K11.behindYesS_at_head_of_Rd
