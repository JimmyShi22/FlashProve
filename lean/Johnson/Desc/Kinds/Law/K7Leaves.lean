-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7Leaves.lean: WHAT THE PLACE OF THE NEXT TOKEN (the quiet entry into the
head's link, then the next token's own sub-protocol, as one sub-protocol) LEAVES OF THE CHAIN's
STATEMENT AND OF WHAT WAS PUT OUT: the oracle messages and the number of the index masks' message
are as they were; every group behind is a group in front or has no member. One theorem.

  place_keeps      by Law/ReplyRest.lean (place_whole: the statement has one fresh group more;
                   reply_rest) and Top/H0/Tw/K2C/FrontGroup.lean
                   (withFresh · headFrontQ_rest).

USER. The field k7 of KeepShares (RoomKeep.lean): the index-mask message's ledger is read
off the oracle messages at that number; its second clause asks that the message is a member of no
group.
A NEAR TWIN IN PART: the clause on the number is place_index
(Law/K7AtMgAll.lean), which stands over the composed meaning's cone; it is typed again here so that
this file stays light.
WHAT IT IS NOT. An implication: hfront (an accept of the entry is an accept of headFrontQ) is a
premise. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReplyRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_rest withFresh)

/-- **What the place keeps.** -/
theorem place_keeps (W : Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → headFrontQ tl s = .ok s1) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      t.st.oracles = s.st.oracles ∧ t.out.indexMasks = s.out.indexMasks ∧
        ∀ G ∈ t.st.groups, G ∈ s.st.groups ∨ G.members = #[] := by
  intro s rs gs t h
  obtain ⟨e1, _⟩ := place_whole W l name front tl hfront s rs gs t h
  refine ⟨by rw [e1]; rfl, ?_, fun G hG => ?_⟩
  · have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind
        fun s1 => (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length)
          (gs.drop front.openings)) = .ok t := h
    cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
    | error e => rw [hp] at h'; cases h'
    | ok s1 =>
      rw [hp] at h'
      obtain ⟨_, _, _, _, _, _, _, _, a9, _⟩ := reply_rest l W.hS.V h'
      rw [a9, (headFrontQ_rest (hfront _ _ _ _ hp)).2.2.2.2.2.1]
  · rw [e1] at hG
    rcases Array.mem_push.1 hG with h1 | rfl
    · exact Or.inl h1
    · exact Or.inr rfl

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.place_keeps
