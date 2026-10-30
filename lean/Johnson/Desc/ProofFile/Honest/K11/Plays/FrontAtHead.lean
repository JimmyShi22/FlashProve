-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/FrontAtHead.lean: the proofs of `HereAtHead`,
`HalfReadyAtHead`, `MaskAtHeadPlain` and `PubTestAtHead`
(Honest/K11/Plays/FrontAtHeadStatement.lean), to the letter. Lemmas; none of the library's goals.

How: calls. The pair gives the library's "reached" at 346 (the frame's `thrS_rchAt`,
Honest/Thread/ReachAtHead.lean); there, without a mark, the library's condition on the state in
front of the merge holds (`P4.waK6_rchAt`, Johnson/P4R/WaK6AtRchAt.lean); so the state stands in the
head's link with what the head heard laid (`heardLaidOfWa`, Honest/K11/ClaimAtHead.lean). The
second: with `ledger_at_head` and `opened_at_head` (LedgerAtHead.lean of this folder). The third:
`maskAt_at_head` (MaskAtHead.lean of this folder) at the frame without a tree and the strings that
hold nothing. The fourth: the member is the kind's block at its seat (`headMergeAtFull`,
Johnson/Desc/K11/Exchange/AtFull.lean); its step's yes is a yes of the kind's decision
(`headMergeSeated`, Johnson/Desc/K11/Returns/Seat.lean; the library's law on the guard on the mark);
then `pubTestOfForm` (Johnson/Desc/K11/Returns/OfForm.lean) at the two tests on the ledger and the
third.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.LedgerAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskAtHead
import Johnson.Desc.ProofFile.Honest.K11.ClaimAtHead
import Johnson.Desc.K11.Returns.Seat
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (step_iff)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open Johnson.Desc.First.ForkMerge.Returns (headMergeSeated pubTestOfForm)
open P5J (F0T)
open ProofFile.Honest.FirstThread (thrS_rchAt lettersHead)

/-- **The state stands in the head's link; what the head heard is laid.** -/
theorem here_at_head : HereAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E hT
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hb : 346 ≤ cF.blocksInOrder.length := by
    obtain ⟨_, _, _, _, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hr : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) 346 ((m.st.input.x.pub, s), ()) :=
    thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w () hb hT
  obtain ⟨hf, _, _⟩ := ledger_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item
    n₁ n₂ b₀ Vd Rd Kp w k s m E Bs O.made hT.1
  exact heardLaidOfWa _ _ s
    (P4.waK6_rchAt h.scope h.reads O h.laid.planOk ((m.st.input.x.pub, s), ()) hr hf)

/-- **The clauses gathered.** -/
theorem halfReady_at_head : HalfReadyAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs
    hmade hT
  obtain ⟨hf, _, _⟩ := ledger_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item
    n₁ n₂ b₀ Vd Rd Kp w k s m E Bs hmade hT.1
  obtain ⟨a, hx, ha, hax⟩ := here_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp w k s m E hT
  obtain ⟨o1, o2, o3, o4⟩ := opened_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp w k s m E Bs a hmade hT.1 ha
  exact ⟨hf, a, hx, ha, o1, hax, o2, o3, o4⟩

/-- **The mask row's sentence, with no frame beside it.** -/
theorem maskAt_head_plain : MaskAtHeadPlain := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k s m E xM
    hxM hT
  exact maskAt_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp
    w k s m E ⟨0, [], id, 0⟩ (fun _ => (0, []), fun _ => []) xM hxM hT

/-- **The public test behind the member's step.** -/
theorem pubTest_at_head : PubTestAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk k s m E
    ds y cols s' hT hS hblk
  obtain ⟨Bs, _, name, hmade, _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  have eb : blk = IM.seatedAs ProofFile.sameReply (headClaimMergeKind (_root_.K11.parOf Zp Bs.G₀)) name
      IM.k11Place := Option.some.inj (hblk.symm.trans hfl)
  subst eb
  obtain ⟨_, e1, e2⟩ := ledger_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item
    n₁ n₂ b₀ Vd Rd Kp w k s m E Bs hmade hT.1
  obtain ⟨xM, hxM⟩ := maskMemberAtHead Z D r Zp Np cF x h
  have hM := maskAt_head_plain Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀
    Vd Rd Kp w k s m E xM hxM hT
  have hd := ((step_iff _ _ s s' _ cols _).1 hS.2).2.1
  rw [headMergeSeated (_root_.K11.parOf Zp Bs.G₀) name IM.k11Place] at hd
  exact pubTestOfForm _ s s' _ _ xM 0 ((IM.guardMark_yes _ s s' _ _).1 hd).1 e1 e2 hM

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.here_at_head
#print axioms ProofFile.Honest.K11.halfReady_at_head
#print axioms ProofFile.Honest.K11.maskAt_head_plain
#print axioms ProofFile.Honest.K11.pubTest_at_head
