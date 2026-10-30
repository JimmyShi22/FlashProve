-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedS.lean: the proofs of `HeadMergeSteppedAt`,
`HeadMergeAcceptedS` and `HeadMergeAcceptedOfGuardS` (Honest/K11/Plays/AcceptedSStatement.lean), to
the letter. Lemmas; none of the library's goals.

How. The first: the lines of `headMergeAccepted` (Accepted.lean of this folder), which spend the
thread in one place alone: to draw "the state is ready"; here that is a premise at the stand.
Accepted.lean keeps its bytes. The second: the first, at each stand at which the pair holds. The
third: the second, with `guardIsReady` (Johnson/Desc/K11/Shape/Step.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedSStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedOfGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Claim noDigest step_iff)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind mergeEntries)
open Johnson.Desc.First.ForkMerge.Returns (headMergeDecideReturns headMergeSeated)
open Johnson.Desc.First.ForkMerge.ShapeStep (guardIsReady)

/-- **At one stand: the member's step says yes.** -/
theorem headMergeSteppedAt : HeadMergeSteppedAt := by
  intro Bk W₀ Rc Xi Tr X Pb T b P claims weights name pl hmem hhalf blk hblk k s m E ds y cols
    hready hd hMv
  have eb : blk = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl := by
    rw [hmem] at hblk
    exact (Option.some.inj hblk).symm
  subst eb
  have hlen : (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl).rounds.length = P.lay.lk + 4 := by
    show ((mergeEntries P.lay.lk 1 P.work).map _).length = _
    rw [List.length_map, mergeEntries_length]
  have hfit := fitsAt_half T hmem hhalf
    ((half_rounds P claims weights).trans hlen.symm)
    (by
      rw [hlen]
      show (List.replicate (P.lay.lk + 4) _).length = _
      rw [List.length_replicate]) _ hmem k m E ds y cols hd hMv
  obtain ⟨hfail, a, claim, x, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := hready
  obtain ⟨wo, G, hdec0, _, _⟩ :=
    headMergeDecideReturns P s a claim x (roundsOf y.1) r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 hfit.1
  obtain ⟨s', hdec, hfail'⟩ : ∃ s', Johnson.Desc.First.ForkMerge.headMergeDecide P s
      ((roundsOf y.1).map noDigest) = .ok s' ∧ s'.failed = none := ⟨_, hdec0, hfail⟩
  have hdec' : (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl).decide s
      ((roundsOf y.1).map noDigest)
      ((IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl).shown T.ft (roundsOf y.1) cols) =
        .ok s' := by
    rw [headMergeSeated P name pl]
    exact (IM.guardMark_yes (headClaimMergeKind P) s s' _ _).2 ⟨hdec, hfail'⟩
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl)
    (rs := roundsOf y.1) (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, ?_⟩
  rw [← hw]
  exact (step_iff T.ft _ s s' (roundsOf y.1) cols _).2 ⟨hfit, hdec', rfl⟩

/-- **From the pair.** -/
theorem headMergeAcceptedS : HeadMergeAcceptedS := by
  intro Bk W₀ Rc Xi Tr X Pb T Said b P claims weights name pl hmem hhalf hready fall blk hblk k s m
    E ds y cols hA hd _ _ hMv
  exact headMergeSteppedAt Bk W₀ Rc Xi Tr X Pb T b P claims weights name pl hmem hhalf blk hblk k s
    m E ds y cols (hready k s m E hA) hd hMv

/-- **From the pair, at the test on the shape.** -/
theorem headMergeAcceptedOfGuardS : HeadMergeAcceptedOfGuardS := by
  intro Bk W₀ Rc Xi Tr X Pb T Said b P claims weights name pl hmem hhalf hg
  exact headMergeAcceptedS Bk W₀ Rc Xi Tr X Pb T Said b P claims weights name pl hmem hhalf
    fun k s m E hT => (readyIsReady P s).2 ((guardIsReady P s).1 (hg k s m E hT))

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.headMergeSteppedAt
#print axioms ProofFile.Honest.K11.headMergeAcceptedS
#print axioms ProofFile.Honest.K11.headMergeAcceptedOfGuardS
