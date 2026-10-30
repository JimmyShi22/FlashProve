-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/Keeps.lean: the proofs of `HeadMergeWrites` and `HeadMergeKeeps`
(Johnson/Desc/K11/Returns/KeepsStatement.lean), to the letter. Lemmas; none of the library's goals.

How. All by the library's own lemmas that take a return apart: the decision's: `decide_inv`
(Johnson/Top/H0/MergeLaw/Says.lean) and `isLocal` (Johnson/Top/H0/MergeLaw/Law.lean); the hearing's:
`mergeHear_inv` (Johnson/Top/H0/MergeLaw/Hear.lean); the laying of one value: `hideRun_one`,
`hide_inv` (Johnson/Top/H0/MergeLaw/Ledger.lean); that the slot was free, and that the link is open:
off the two texts (`hide_wasFree`, `decide_opened`). At the seat: `headMergeSeated` (Seat.lean of
this folder) and `IM.guardMark_yes` (Johnson/IMR/SeatForm.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.KeepsStatement
import Johnson.Desc.K11.Returns.Seat
import Johnson.Top.H0.MergeLaw.Ledger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes.PscRun (Filled)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (decide_inv mergeHear_inv isLocal hideRun_one hide_inv)

/-- A value is laid under a free slot alone. -/
theorem hide_wasFree {F G : OnBytes.Model.Fork} {j : Nat} {v b : OnBytes.E}
    (h : F.hide j v b = some G) : ¬ Filled F j := by
  unfold OnBytes.Model.Fork.hide at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hc
    intro hf
    unfold Filled at hf
    have hsz : j < F.gotF.size := by
      rw [hc.1.2]
      exact hc.1.1
    have e : F.gotF.getD j true = F.gotF.getD j false := by
      simp [Array.getD_eq_getD_getElem?, hsz]
    rw [← e, hc.2] at hf
    cases hf
  · cases h

/-- The decision returns at an open link alone. -/
theorem decide_opened {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView} {a : HeadOwn}
    (h : headMergeDecide P s rs = .ok s') (ha : s.here = .head a) : a.opened = true := by
  by_cases ho : a.opened = true
  · exact ho
  · simp [headMergeDecide, ha, ho, VerifiableInference.Desc.need, bind, Except.bind] at h

/-- **What the decision writes.** -/
theorem headMergeWrites : HeadMergeWrites := by
  intro P s s' rs h
  obtain ⟨a, a', tp, F, claim, x, wo, h1, h2, _, _, h5, _, h7, h8, h9, _, h11⟩ := decide_inv h
  obtain ⟨b, b', e1, e2, e3, e4, _⟩ := isLocal P s rs s' h
  have eb : b = a := by
    rw [h1] at e1
    exact (VerifiableInference.Desc.First.Here.head.inj e1).symm
  have eb' : b' = a' := by
    rw [h2] at e2
    exact (VerifiableInference.Desc.First.Here.head.inj e2).symm
  subst eb
  subst eb'
  obtain ⟨_, _, _, _, beta, v, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsFv, hhide, _⟩ :=
    mergeHear_inv h7
  obtain ⟨g1, g2, hF⟩ := hide_inv (hideRun_one hhide)
  have g3 := hide_wasFree (hideRun_one hhide)
  have ej : wo.sFv = mergeEndSlot P.lay.lk b.F := by
    rw [hsFv]
    unfold mergeEndSlot
    omega
  have en : b.F.next + 1 + 2 * P.lay.lk + 2 = b.F.next + 2 * P.lay.lk + 3 := by omega
  rw [ej] at g1 g3
  rw [ej, en] at hF
  refine ⟨b, wo, v, beta, h1, decide_opened h h1, g1, g2, g3, ?_, ?_⟩
  · rw [← h11, hF]
  · rw [e3, e4, h5, h8, h9, hF]

/-- **What the member's step leaves and turns.** -/
theorem headMergeKeeps : HeadMergeKeeps := by
  intro P name pl s s' rs gs h
  rw [headMergeSeated P name pl] at h
  obtain ⟨h1, h2⟩ := (IM.guardMark_yes (headClaimMergeKind P) s s' rs gs).1 h
  exact ⟨headMergeWrites P s s' rs h1, h2⟩

end Johnson.Desc.First.ForkMerge.Returns

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Returns.hide_wasFree
#print axioms Johnson.Desc.First.ForkMerge.Returns.decide_opened
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeWrites
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeKeeps
