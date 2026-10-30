-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/OfForm.lean: the proofs of `HeadMergeKeepsOfStep`, `FreeAboveOfForm`,
`PubBehindMerge` and `PubTestOfForm` (Johnson/Desc/K11/Returns/OfFormStatement.lean), to the letter.
Lemmas; none of the library's goals.

How. A step's yes holds a yes of the block's decision (`stepYes_decide`,
Johnson/Top/H0/Walk/ReachInv.lean); then `headMergeKeeps` (Keeps.lean of this folder). At a head the
reader of the open ledger answers just where the link is open (Johnson/Desc/First/State.lean): so
the two tests speak of the head's own ledger; a mark beyond the array's size reads as free. Behind
the merge: the kind's clause writes the state out: the arrays are set in place, the number of slots
stands, and the next free number is the plan's number of slots: no slot is left to ask of. The test
on forms: the library's own `merge_makes_formsIn` (Johnson/Top/H0/MergeLaw/MergeMakesForms.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.OfFormStatement
import Johnson.Desc.K11.Returns.Keeps
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes.PscRun (Sized Filled FreeAbove)
open VerifiableInference.Desc.First (S HeadOwn ledgerB freeAboveB)
open VerifiableInference.Desc.First.MergeLaw (merge_makes_formsIn frontR)
open Johnson.Desc.First.Walk.Tied (stepYes_decide)

/-- **The kind's clause, from the whole member's accepting step.** -/
theorem headMergeKeepsOfStep : HeadMergeKeepsOfStep := by
  intro ft P name pl s s' h
  obtain ⟨rs, gs, e⟩ := stepYes_decide h
  exact headMergeKeeps P name pl s s' rs gs e

/-- **What the two tests give at a head.** -/
theorem freeAboveOfForm : FreeAboveOfForm := by
  intro n s a ha hl hf
  have ho : a.opened = true := by
    cases hb : a.opened with
    | true => rfl
    | false => simp [ledgerB, S.fork?, ha, hb] at hl
  have hk : s.fork? = some a.F := by simp [S.fork?, ha, ho]
  simp only [ledgerB, hk, Option.any_some, Bool.and_eq_true, beq_iff_eq] at hl
  simp only [freeAboveB, hk, Option.any_some, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hf
  refine ⟨ho, ⟨hl.1.1, hl.1.2, hl.2⟩, hf.2, ?_⟩
  intro j hj hF
  unfold Filled at hF
  by_cases hlt : j < a.F.ns
  · have h1 := hf.1 (j - a.F.next) (by omega)
    have e : a.F.next + (j - a.F.next) = j := by omega
    rw [e] at h1
    have hs : j < a.F.gotF.size := by rw [hl.2]; exact hlt
    simp [Array.getD, hs] at h1 hF
    rw [h1] at hF
    cases hF
  · have hs : ¬ j < a.F.gotF.size := by rw [hl.2]; exact hlt
    simp [Array.getD, hs] at hF

/-- **The two tests behind the merge.** -/
theorem pubBehindMerge : PubBehindMerge := by
  intro P s s' hK hl hf
  obtain ⟨⟨a, wo, v, β, ha, ho, _, _, _, hn, e⟩, _⟩ := hK
  obtain ⟨_, ⟨z1, z2, z3⟩, hns, _⟩ := freeAboveOfForm P.nMsg s a ha hl hf
  subst e
  constructor
  · simp [ledgerB, S.fork?, ho, z1, z2, z3]
  · simp [freeAboveB, S.fork?, ho, hns, hn]

/-- **The test on forms at the merge's own run.** -/
theorem pubTestOfForm : PubTestOfForm := by
  intro P s s' rs own xM R h hl hf hM
  refine merge_makes_formsIn P h ?_ ?_ own xM R hM
  · unfold frontR
    cases hh : s.here with
    | head a =>
      obtain ⟨_, ⟨z1, z2, z3⟩, hns, _⟩ := freeAboveOfForm P.nMsg s a hh hl hf
      simp [z1, z2, z3, hns]
    | _ => rfl
  · intro a ha
    exact (freeAboveOfForm P.nMsg s a ha hl hf).2.2.2

end Johnson.Desc.First.ForkMerge.Returns

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeKeepsOfStep
#print axioms Johnson.Desc.First.ForkMerge.Returns.freeAboveOfForm
#print axioms Johnson.Desc.First.ForkMerge.Returns.pubBehindMerge
#print axioms Johnson.Desc.First.ForkMerge.Returns.pubTestOfForm
