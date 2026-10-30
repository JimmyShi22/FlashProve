-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LedgerAtHead.lean: the proofs of `LedgerAtHead` and
`OpenedAtHead` (Honest/K11/Plays/LedgerAtHeadStatement.lean), to the letter. Lemmas; none of the
library's goals.

How: calls. The mark: the thread's own public form. The two tests: every public item that is open at
the border holds of the state wherever the thread holds (the frame's `thr_pub`,
Honest/Thread/FormLaw.lean); that "ledger 24" and "freeAbove 24" are open at 346: the library's
`k11_six` (Johnson/Desc/Sound/MgAt/K11Closed.lean); that the table's number of slots at segment 24
is the kind's: `nums_of_test` (Johnson/Top/H0/MergeLaw/PlanNumsAt.lean) at the test that the head
pays (`numsB_head_of_public`, Johnson/Desc/Sound/K11Tests/NumsHeadInScope.lean), as
Johnson/K11R/CondOfTight.lean calls it. The second lemma: `freeAboveOfForm`
(Johnson/Desc/K11/Returns/OfForm.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.LedgerAtHeadStatement
import Johnson.Desc.K11.Returns.OfForm
import Johnson.Desc.Sound.MgAt.K11Closed
import Johnson.Desc.Sound.K11Tests.NumsHeadInScope
import Johnson.Top.H0.MergeLaw.PlanNumsAt
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.First (freeAboveB)
open VerifiableInference.Desc.Sound (k11_six mgBase)
open VerifiableInference.Desc.First.MergeLaw (nums_of_test)
open Johnson.Desc.First.ForkMerge.Returns (freeAboveOfForm)
open ProofFile.Honest.FirstThread (thr_pub lettersHead)

set_option maxRecDepth 100000 in
/-- **No mark, and the table's two tests on the ledger.** -/
theorem ledger_at_head : LedgerAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    hmade hT
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := (IM.base_made hmade).2.2.1
  have tn := LT28.K11Tests.numsB_head_of_public h.scope h.reads h.laid.pub h.pubOne
    (Nat.pow_right_injective (le_refl 2) (h.cols13.trans (by decide +kernel)))
  obtain ⟨n1, _, _⟩ := nums_of_test hG tn
  obtain ⟨_, _, _, c4, c5, _⟩ := k11_six h.𝔇 mgBase rfl rfl
  have e1 := thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT c4
  have e2 := thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT c5
  have e2' : ((h.𝔇.pubD.nsOf 24).any fun n => freeAboveB n s) = true := e2
  have hns : h.𝔇.pubD.nsOf 24 = some (_root_.K11.parOf Zp Bs.G₀).nMsg := n1
  rw [hns] at e2'
  have hThr := hT
  unfold Thr at hThr
  obtain ⟨-, -, ⟨hf, -⟩, -, -, -, -⟩ := hThr
  have hf0 : s.failed.isNone = true := hf
  have hf' : s.failed = none := by
    cases hs : s.failed with
    | none => rfl
    | some e =>
      rw [hs] at hf0
      cases hf0
  exact ⟨hf', e1, e2'⟩

/-- **Opened; the sizes; the number of slots; free from the next free number on.** -/
theorem opened_at_head : OpenedAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    a hmade hT ha
  obtain ⟨_, e1, e2⟩ := ledger_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item
    n₁ n₂ b₀ Vd Rd Kp w k s m E Bs hmade hT
  exact freeAboveOfForm _ s a ha e1 e2

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.ledger_at_head
#print axioms ProofFile.Honest.K11.opened_at_head
