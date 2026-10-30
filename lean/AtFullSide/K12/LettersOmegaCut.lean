-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LettersOmegaCut.lean: at the written book the public test cutFits at Omega's entry of
the last chain's test: so sameCut_of_book (K12/CutOfBook.lean) gives the premise same of wordsAt_member
at Omega's member.

  cutFits_omega_at_W   cutFits at number 2 of either part of the pair
  same_at_W      SameCut at Omega's member, at the coins that the row hands the test

By what. written_O (HeldAtHeadW.lean), carryE_at_W.

Limits.
- hq: the member's row is the written row. ht, htf, hte: the sender's count holds that row.
- hown, hd in same_at_W: the sending's own cut, and the book's row at the sender.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.HeldAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook
import Johnson.Desc.ProofFile.Honest.K12.AtProof.MakerBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open AtFullSide.K14 (rawBookRows_written rawWhole_is_raw)

/-- **The public test at Omega's entry, at either part of the pair.** -/
theorem cutFits_omega_at_W {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {j : Nat} (hj : j ∈ [0, 1])
    (J : ProofFile.Honest.K14.SendJob) (hq : msgOf senderO J 0 = rowOF)
    (ht : rowOF.2.2.e ≤ (ProofFile.Honest.K14.takesOf J.Q.codes J.Q.sent J.sort).e) :
    ProofFile.Honest.K12.Light.cutFits B ⟨placeW, j⟩ 2 senderO J 0 = true := by
  obtain ⟨-, -, hAll, -, -⟩ := written_O
  have hL := hAll j hj
  have ha : (⟨placeW, j⟩ : Addr) = ⟨placeW, 0⟩ ∨ (⟨placeW, j⟩ : Addr) = ⟨placeW, 1⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hc := carryE_at_W hB ha
  rw [List.getElem?_map] at hL
  obtain ⟨e, he, q⟩ := Option.map_eq_some_iff.1 hL
  obtain ⟨o, s, c⟩ : e.owner = senderO ∧ e.start = ⟨0, 0⟩ ∧ e.count = rowOF.2.2 := by
    simpa [Prod.mk.injEq] using q
  have he' : (ProofFile.Honest.K12.Light.carriedOf B ⟨placeW, j⟩)[2]? = some e := by
    show (carryE B _)[2]? = _
    rw [hc]
    exact he
  have e₁ : (msgOf senderO J 0).2.2.e = rowOF.2.2.e :=
    congrArg (fun r : Addr × Nat × Due => r.2.2.e) hq
  have e₂ : (msgOf senderO J 0).2.2.e =
      ProofFile.Honest.K14.dueOf J.Q.codes (J.Q.sent.getD 0 default).shape (J.sort 0) := rfl
  unfold ProofFile.Honest.K12.Light.cutFits
  rw [he']
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨o, ?_⟩, ?_⟩, ?_⟩
  · rw [s]
    rfl
  · rw [c]
    exact e₁.symm.trans e₂
  · rw [s, c]
    simpa using ht

variable {V W X : Type}

/-- **At the coins that the row hands the test, Omega's member's stretch is the sending's own cut.**
hq: the member's row is the written row; hd: the book's row at the sender is what it takes. -/
theorem same_at_W {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) (J : ProofFile.Honest.K14.SendJob) (hq : msgOf senderO J 0 = rowOF)
    (Mj : TestJob W X) (hp : Mj.p.place = placeW) (k : Coins B)
    (c : RowCoins [(firstPart Mj : Part V W X), restPart Mj])
    (hl : lendRow B (B.rowsOf 2) (k.look 2) Mj.p.place
      [(firstPart Mj : Part V W X), restPart Mj] 0 = .ok c)
    (own : Cs (ProofFile.Honest.K14.takesOf J.Q.codes J.Q.sent J.sort))
    (hown : (k.look 1 senderO).2.cut ⟨0, 0⟩ (ProofFile.Honest.K14.takesOf J.Q.codes J.Q.sent J.sort) =
      some own)
    (hd : dueAt B.shared senderO = ProofFile.Honest.K14.takesOf J.Q.codes J.Q.sent J.sort)
    (htf : rowOF.2.2.f ≤ (ProofFile.Honest.K14.takesOf J.Q.codes J.Q.sent J.sort).f)
    (hte : rowOF.2.2.e ≤ (ProofFile.Honest.K14.takesOf J.Q.codes J.Q.sent J.sort).e) :
    ProofFile.Honest.K12.Light.SameCut J 0 (coinsE own).toArray ((restCoins Mj c.2.1).mem 2) := by
  obtain ⟨-, hl'⟩ := lendRow_cons_ok hl
  obtain ⟨l1, -⟩ := lendRow_cons_ok hl'
  rw [hp] at l1
  obtain ⟨t1, t3, hAll, -, -⟩ := written_O
  have hL := hAll 1 (by decide)
  obtain ⟨-, r2, r3⟩ := rawBookRows_written _ B (rawWhole_is_raw hB)
  have hc := carryE_at_W hB (a := ⟨placeW, 1⟩) (Or.inr rfl)
  rw [List.getElem?_map] at hL
  obtain ⟨e, he, q⟩ := Option.map_eq_some_iff.1 hL
  obtain ⟨o, s, c'⟩ : e.owner = senderO ∧ e.start = ⟨0, 0⟩ ∧ e.count = rowOF.2.2 := by
    simpa [Prod.mk.injEq] using q
  have he' : (carryE B ⟨placeW, 1⟩)[2]? = some e := by
    rw [hc]
    exact he
  have key := member_held_shared k l1 he' (t := ProofFile.Honest.K14.takesOf J.Q.codes J.Q.sent J.sort)
    (by rw [o]; exact hd) (by rw [o, (rawBookRows_written _ B (rawWhole_is_raw hB)).1]; exact t1)
    (by rw [o, r3]; exact t3) s (by rw [c']; exact htf)
    (by rw [c']; exact hte) (by rw [o]; exact hown)
  intro i hi
  have e₁ : (msgOf senderO J 0).2.2.e = rowOF.2.2.e :=
    congrArg (fun r : Addr × Nat × Due => r.2.2.e) hq
  have e₂ : (msgOf senderO J 0).2.2.e =
      ProofFile.Honest.K14.dueOf J.Q.codes (J.Q.sent.getD 0 default).shape (J.sort 0) := rfl
  have hi' : i < e.count.e := by
    rw [c', ← e₁, e₂]
    exact hi
  have hj : i < (ProofFile.Honest.K14.takesOf J.Q.codes J.Q.sent J.sort).e := by
    rw [c'] at hi'
    omega
  show OnBytes.Slice.readE ((coinsE own).toArray.getD (0 + i) OnBytes.zeroE) = _
  rw [Nat.zero_add, ProofFile.Honest.K12.Light.coinsE_at own _ hj]
  exact (key i hi').symm

end AtFullSide.K12

#print axioms AtFullSide.K12.same_at_W
#print axioms AtFullSide.K12.cutFits_omega_at_W
