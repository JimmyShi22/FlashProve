-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SixRide.lean: the proof of `SixFormsRideAtHead`
(Honest/K11/Plays/SixRideStatement.lean), to the letter. A lemma; none of the library's goals.

How. `formsRide_at_head` (FormsRide.lean of this folder) at each of the six names; none is "weights"
(by `decide`). Its premise on the runs: `passAtSix` at `runsPassAtReached`
(Johnson/Desc/K11/Across/PassAtSix.lean). What that takes: "reached": the pair gives it (the frame's
`thrS_reach_below`; the library's `reach_raw`) · the eight public tests of `keep24`: each is, by the
library's closed fact `k11_hIn` (Johnson/Top/H0/MergeLaw/K11PubClosed.lean), among the public items
that are open at 346 or among those tied to an item that is open there: the thread's form holds both
sorts (the frame's `thr_pub`, `thr_pubI`) · the test on the ledger: `ledger_at_head`
(LedgerAtHead.lean of this folder) · the yes: the stronger clause holds it.

Limits. Those of the statement. ONE RAISED OPTION stands in front of the theorem (maxRecDepth
100000), as in front of `ledger_at_head`. `smallRides_at_head` (SmallRides.lean of this folder) is
an instance of this lemma, at (6, "small"): it stands for its lighter ground: one call of the
library's. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.SixRideStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.FormsRide
import Johnson.Desc.ProofFile.Honest.K11.Plays.LedgerAtHead
import Johnson.Desc.ProofFile.Honest.Thread.FormLawI
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.K11.Across.PassAtSix
import Johnson.Desc.K11.Exchange.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.First.MergeLaw (sixNames)
open VerifiableInference.Desc.Sound (mgAll mgBase keep24 k11_hIn)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open Johnson.Desc.First.ForkMerge.Across (passAtSix runsPassAtReached)
open ProofFile.Honest.FirstThread (lettersHead thr_pub thr_pubI thrS_reach_below)

set_option maxRecDepth 100000 in
/-- **All six ride past the merge's member.** -/
theorem sixFormsRide_at_head : SixFormsRideAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    hB hk y hy
  have hne : ∀ u ∈ sixNames, u.2 ≠ "weights" := by decide
  refine formsRide_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd
    Rd Kp w Bs y.1 y.2 (hne y hy) hB hk ?_
  intro k s m E s' hT hK p hp
  obtain ⟨_, rs, hyes⟩ := hk s s' hK
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hr := reach_raw (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
  have hq : ∀ q ∈ keep24, (mgAll h.𝔇 mgBase).pub q (m.st.input.x.pub, s) = true := by
    intro q hq
    rcases List.mem_append.1 (k11_hIn h.𝔇 mgBase rfl q (List.mem_append_right _ hq)) with h1 | h1
    · exact thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT.1 h1
    · exact thr_pubI (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT.1 h1
  obtain ⟨_, hled, _⟩ := ledger_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item
    n₁ n₂ b₀ Vd Rd Kp w k s m E Bs hB hT.1
  exact passAtSix _ _ _ _ _ _ _ h.𝔇 rfl (_root_.K11.parOf Zp Bs.G₀) s s' rs hyes
    (runsPassAtReached Z D r Zp Np cF x h (_root_.K11.parOf Zp Bs.G₀) m.st.input.x.pub s s' rs hr hq
      hled hyes) y hy p hp

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.sixFormsRide_at_head
