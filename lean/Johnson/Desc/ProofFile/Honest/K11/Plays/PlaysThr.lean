-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/PlaysThr.lean: the proofs of `HeadMergePlaysThr` and
`HeadMergePlaysSeated` (Honest/K11/Plays/PlaysThrStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The member is the kind's block at its seat; the frame's steps for it are the row's: so the play
returns (`headMergePlays`), and the rounds read no column (`headMergeNoRead`; both
Honest/K11/Plays/Proofs.lean). The block states no oracle message, so that as many trees are at hand
behind it as in front (`treesTo_succ`, Honest/Thread/MadeLaw.lean): no source is new.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.PlaysThrStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Proofs
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)

/-- Empty lists, laid in a row, are the empty list. -/
theorem flat_replicate_nil {α : Type} : ∀ n : Nat,
    (List.replicate n ([] : List α)).flatMap id = []
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatMap_cons]
    exact flat_replicate_nil n

/-- **It plays.** -/
theorem headMergePlaysThr : HeadMergePlaysThr := by
  intro Bk W₀ Rc Xi Tr X Pb T b P claims weights name pl coins hmem hsteps blk hblk k s m E ds st hT
    hd _ hst
  have eb : blk = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl := by
    rw [hmem] at hblk
    exact (Option.some.inj hblk).symm
  subst eb
  obtain ⟨v, q, rfl⟩ := hsteps k m.st.input st hst
  cases ds with
  | nil => cases hd
  | cons d₀ ds₁ =>
    have hp := headMergePlays W₀ Rc Xi Tr X S Claim
      (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) P claims weights v q (coins k) d₀ ds₁ [] m
      rfl rfl hd
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

/-- **It plays, under the whole structure.** -/
theorem headMergePlaysSeated : HeadMergePlaysSeated := by
  intro Bk W₀ Rc Xi Tr X Pb Pp Tok Xi' rows cols nR Xp T b P claims weights name pl coins i₁ i₂ toP
    toW Dof Mg₀ seg l H
  exact headMergePlaysThr Bk W₀ Rc Xi Tr X Pb T b P claims weights name pl coins H.member H.steps

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.flat_replicate_nil
#print axioms ProofFile.Honest.K11.headMergePlaysThr
#print axioms ProofFile.Honest.K11.headMergePlaysSeated
