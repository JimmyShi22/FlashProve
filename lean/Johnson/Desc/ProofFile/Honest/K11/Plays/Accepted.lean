-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/Accepted.lean: the proofs of `StepsOfHalf`,
`HeadMergePlaysHalf` and `HeadMergeAccepted` (Honest/K11/Plays/AcceptedStatement.lean), to the
letter. Lemmas; none of the library's goals.

How. The frame's steps for one member at which a half stands are that half's, at what the book lends
(`steps_one_half`, Honest/Law/Thread.lean). It plays: as in Honest/K11/Plays/PlaysThr.lean. The yes:
what was played and read passes the step's own tests on rounds and columns (`fitsAt_half`,
Honest/Thread/ShapeRow.lean); the decision returns at a state that is ready
(`headMergeDecideReturns`, Johnson/Desc/K11/Returns/Decide.lean), and leaves the mark as it was; the
seated block is the marked block (`headMergeSeated`, Johnson/Desc/K11/Returns/Seat.lean;
`IM.guardMark_yes`, Johnson/IMR/SeatForm.lean); the step is laid together as in `accepted_of_shape`
(Honest/Thread/Shape.lean): `want_length`, and the library's `step_iff`
(Johnson/Top/H0/StepLaws/StepLaws.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.PlaysThr
import Johnson.Desc.ProofFile.Honest.Thread.ShapeRow
import Johnson.Desc.K11.Returns.Decide
import Johnson.Desc.K11.Returns.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Claim noDigest step_iff)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind mergeEntries)
open Johnson.Desc.First.ForkMerge.Returns (headMergeDecideReturns headMergeSeated)
open ProofFile.Honest.SumLaw (lift_moves_count)

/-- **The steps, from the half.** -/
theorem stepsOfHalf : StepsOfHalf := by
  intro Bk W₀ Rc Xi Tr X Pb T P claims weights name pl hhalf k w st hst
  obtain ⟨c, hc, rfl⟩ :=
    steps_one_half (b := IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) hhalf hst
  exact ⟨c.1.1, c.2.1, hc, rfl⟩

/-- The row has as many rounds as the kind's block. -/
theorem half_rounds {W₀ Rc Xi Tr X : Type} (P : Johnson.Desc.First.ForkMerge.HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List OnBytes.Model.WsClaim) (weights : W₀ → Weights) :
    (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).rounds = P.lay.lk + 4 := by
  show 0 + 1 + (headMergeSum (Rc := Rc) (Tr := Tr) (X := X) P claims weights).moves.length = _
  unfold headMergeSum
  rw [lift_moves_count]
  show 0 + 1 + ((List.replicate P.lay.lk _).length + 3) = _
  rw [List.length_replicate]
  omega

/-- **It plays, from the half.** -/
theorem headMergePlaysHalf : HeadMergePlaysHalf := by
  intro Bk W₀ Rc Xi Tr X Pb T b P claims weights name pl hmem hhalf blk hblk k s m E ds st hT hd _
    hst
  have eb : blk = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl := by
    rw [hmem] at hblk
    exact (Option.some.inj hblk).symm
  subst eb
  obtain ⟨q, c, _, rfl⟩ :=
    stepsOfHalf Bk W₀ Rc Xi Tr X Pb T P claims weights name pl hhalf k m.st.input st hst
  cases ds with
  | nil => cases hd
  | cons d₀ ds₁ =>
    have hp := headMergePlays W₀ Rc Xi Tr X S Claim
      (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) P claims weights
      (T.φ.sees m.st.input) q c d₀ ds₁ [] m rfl rfl hd
    refine ⟨_, [], ⟨⟨_, hst, hp⟩, ?_⟩, ?_⟩
    · exact (headMergeNoRead P name pl d₀ [] T.chain T.ft _ _ (d₀ :: ds₁) []).2
    · intro σ hσ
      exfalso
      have e : T.hand (b + 1) = T.hand b := by
        unfold Thread.hand
        rw [treesTo_succ hmem]
        show _ ++ (List.range (treesTo T.bs b +
          ((List.replicate (P.lay.lk + 4) ([] : List _)).flatMap id).length)).map _ = _
        rw [flat_replicate_nil]
        rfl
      obtain ⟨h1, h2⟩ := List.mem_filter.1 hσ
      rw [e] at h1
      simp [h1] at h2

/-- **The member's step says yes.** -/
theorem headMergeAccepted : HeadMergeAccepted := by
  intro Bk W₀ Rc Xi Tr X Pb T b P claims weights name pl hmem hhalf hready fall blk hblk k s m E ds
    y cols hA hd _ _ hMv
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
  obtain ⟨hfail, a, claim, x, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := hready k s m E hA
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

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.stepsOfHalf
#print axioms ProofFile.Honest.K11.half_rounds
#print axioms ProofFile.Honest.K11.headMergePlaysHalf
#print axioms ProofFile.Honest.K11.headMergeAccepted
