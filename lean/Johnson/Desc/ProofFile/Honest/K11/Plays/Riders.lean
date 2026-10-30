-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/Riders.lean: the proofs of `HeadMergeLaysOf`,
`HeadMergeLaysWo`, `HeadStaysPastMerge` and `HeadMergeBehindOf`
(Honest/K11/Plays/RidersStatement.lean), to the letter. Lemmas; none of the library's goals.

How. A step's yes holds the decision's yes (the library's `step_iff`,
Johnson/Top/H0/StepLaws/StepLaws.lean); the seated block's yes gives the kind's clause
(`headMergeKeeps`, Johnson/Desc/K11/Returns/Keeps.lean), whose equation writes the state behind out:
the head's own part with four fields turned, one of them "what the merge left", laid. `Behind`: by
`behind_of_keeps` (Honest/Thread/Riders.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.RidersStatement
import Johnson.Desc.K11.Returns.Keeps
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Claim Place step_iff)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.Returns (K11Keeps headMergeKeeps)

/-- The member's step, its yes in hand, gives the kind's clause. -/
theorem keeps_of_stepped {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk S Claim V W X Pb) {b : Nat}
    {P : HeadMergeP} {name : String} {pl : Place}
    (hmem : T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl))
    {blk k s m E ds y cols s'} (hblk : T.bs[b]? = some blk)
    (hS : T.Stepped blk k s m E ds y cols s') : K11Keeps P s s' := by
  have eb : blk = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl := by
    rw [hmem] at hblk
    exact (Option.some.inj hblk).symm
  subst eb
  exact headMergeKeeps P name pl s s' _ _ ((step_iff T.ft _ s s' _ cols _).1 hS.2).2.1

/-- **Every clause of that sort which the kind's clause gives.** -/
theorem headMergeLaysOf : HeadMergeLaysOf := by
  intro Bk V W X Pb T b P name pl lo hi Q hmem hQ blk hblk k s m E ds y cols s' _ _ hS
  exact hQ s s' (keeps_of_stepped T hmem hblk hS)

/-- **The clause that the member lays.** -/
theorem headMergeLaysWo : HeadMergeLaysWo := by
  intro Bk V W X Pb T b P name pl lo hi hmem
  refine headMergeLaysOf Bk V W X Pb T b P name pl lo hi _ hmem ?_
  intro s s' hK
  obtain ⟨⟨a, wo, v, β, _, _, _, _, _, _, e⟩, _⟩ := hK
  rw [e]
  exact ⟨_, rfl, rfl⟩

/-- **What of the head's own part stays.** -/
theorem headStaysPastMerge : HeadStaysPastMerge := by
  intro P s s' Q hQ hK h0
  obtain ⟨⟨a, wo, v, β, ha, _, _, _, _, _, e⟩, _⟩ := hK
  obtain ⟨a0, ha0, hq⟩ := h0
  obtain rfl : a = a0 := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans ha0)
  rw [e]
  exact ⟨_, rfl, hQ a _ _ _ _ hq⟩

/-- **`Behind`, where the rider is a list of clauses.** -/
theorem headMergeBehindOf : HeadMergeBehindOf := by
  intro Bk V W X Pb T b P name pl cs hmem hrides hkeeps hform hformP hstays hlaid
  refine behind_of_keeps T hrides ?_ hstays ?_
  · intro blk hblk k s m E ds y cols s' hT _ hS
    have hK := keeps_of_stepped T hmem hblk hS
    exact ⟨⟨hform blk k s m E ds y cols s' hT hS hblk hK,
      hformP blk k s m E ds y cols s' hT hS hblk hK⟩, hkeeps s s' hK⟩
  · intro c hc e
    obtain ⟨hi, Q, rfl, hQ⟩ := hlaid c hc e
    exact headMergeLaysOf Bk V W X Pb T b P name pl (b + 1) hi Q hmem hQ

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.keeps_of_stepped
#print axioms ProofFile.Honest.K11.headMergeLaysOf
#print axioms ProofFile.Honest.K11.headMergeLaysWo
#print axioms ProofFile.Honest.K11.headStaysPastMerge
#print axioms ProofFile.Honest.K11.headMergeBehindOf
